"""Compile a local Lean import closure with a bounded number of processes.

Lake supplies the pinned toolchain and dependency environment. This module
only schedules the repository's own Lean sources; dependency OLeans should be
downloaded first with ``lake exe cache get``.
"""

from __future__ import annotations

from concurrent.futures import FIRST_COMPLETED, ThreadPoolExecutor, wait
import json
import os
from pathlib import Path
import re
import shutil
import subprocess
import tempfile


ROOT = Path(__file__).resolve().parents[1]
SOURCE_IMPORT = re.compile(r"^\s*(?:(?:public|private)\s+)?import\s+([A-Za-z0-9_'.]+)\s*$")
IMPORT_START = re.compile(r"^\s*(?:(?:public|private)\s+)?import(?:\s|$)")
LOCAL_ROOTS = frozenset({"Challenge", "Solutions", "Verification", "WeightedEdgeColoring"})
PIN_FILES = tuple(ROOT / name for name in ("lake-manifest.json", "lakefile.lean", "lean-toolchain"))


def artifact(directory: Path, module: str, suffix: str) -> Path:
    return directory.joinpath(*module.split(".")).with_suffix(suffix)


def source(module: str) -> Path:
    return artifact(ROOT, module, ".lean")


def lake_environment(output: Path) -> tuple[dict[str, str], str, list[Path]]:
    result = subprocess.run(
        ["lake", "--quiet", "env", "python3", "-c",
         "import json, os; print(json.dumps(dict(os.environ)))"],
        cwd=ROOT, text=True, capture_output=True, check=True,
    )
    environment = json.loads(result.stdout)
    lean = shutil.which("lean", path=environment.get("PATH"))
    if lean is None:
        raise RuntimeError("Lake's environment does not contain the pinned Lean executable")
    paths = []
    for part in environment.get("LEAN_PATH", "").split(os.pathsep):
        if part:
            path = Path(part)
            paths.append(path if path.is_absolute() else ROOT / path)
    environment["LEAN_PATH"] = os.pathsep.join([str(output), *(str(path) for path in paths)])
    return environment, lean, paths


def dependency_graph(target: str, paths: list[Path]) -> tuple[
    list[str], dict[str, tuple[str, ...]], dict[str, tuple[Path, ...]]
]:
    order: list[str] = []
    graph: dict[str, tuple[str, ...]] = {}
    external: dict[str, tuple[Path, ...]] = {}
    visiting: list[str] = []
    visited: set[str] = set()

    def visit(module: str) -> None:
        if module in visiting:
            cycle = " -> ".join([*visiting[visiting.index(module):], module])
            raise RuntimeError(f"local import cycle: {cycle}")
        if module in visited:
            return
        path = source(module)
        if not path.is_file():
            raise RuntimeError(f"missing local source: {module}")
        visiting.append(module)
        dependencies = []
        external_imports = []
        for number, line in enumerate(path.read_text().splitlines(), start=1):
            match = SOURCE_IMPORT.fullmatch(line)
            if match is None:
                if IMPORT_START.match(line):
                    raise RuntimeError(f"unsupported import syntax at {path}:{number}: {line.strip()}")
                continue
            imported = match.group(1)
            if source(imported).is_file():
                dependencies.append(imported)
            elif imported.split(".", 1)[0] in LOCAL_ROOTS:
                raise RuntimeError(f"{module} imports missing local source {imported}")
            else:
                found = next((artifact(directory, imported, ".olean") for directory in paths
                              if artifact(directory, imported, ".olean").is_file()), None)
                if found is None:
                    raise RuntimeError(
                        f"{module} imports unavailable dependency {imported}; run --fetch-cache"
                    )
                external_imports.append(found)
        graph[module] = tuple(dependencies)
        external[module] = tuple(external_imports)
        for imported in dependencies:
            visit(imported)
        visiting.pop()
        visited.add(module)
        order.append(module)

    visit(target)
    return order, graph, external


def fresh(output: Path, module: str, dependencies: tuple[str, ...],
          external_imports: tuple[Path, ...]) -> bool:
    olean = artifact(output, module, ".olean")
    ilean = artifact(output, module, ".ilean")
    required = [source(module), *PIN_FILES, *external_imports]
    for dependency in dependencies:
        required.extend((artifact(output, dependency, ".olean"),
                         artifact(output, dependency, ".ilean")))
    if any(not path.is_file() for path in [olean, ilean, *required]):
        return False
    latest_input = max(path.stat().st_mtime_ns for path in required)
    return min(olean.stat().st_mtime_ns, ilean.stat().st_mtime_ns) >= latest_input


def compile_one(module: str, output: Path, staging: Path,
                environment: dict[str, str], lean: str) -> tuple[int, str]:
    staged_olean = artifact(staging, module, ".olean")
    staged_ilean = artifact(staging, module, ".ilean")
    staged_olean.parent.mkdir(parents=True, exist_ok=True)
    command = [lean, "-j", "1", "-R", str(ROOT),
               "-o", str(staged_olean), "-i", str(staged_ilean), str(source(module))]
    result = subprocess.run(command, cwd=ROOT, env=environment,
                            text=True, stdout=subprocess.PIPE, stderr=subprocess.STDOUT)
    if result.returncode:
        return result.returncode, result.stdout
    if not staged_olean.is_file() or not staged_ilean.is_file():
        return 1, "Lean succeeded without writing both OLean and ILean artifacts"
    final_olean = artifact(output, module, ".olean")
    final_ilean = artifact(output, module, ".ilean")
    final_olean.parent.mkdir(parents=True, exist_ok=True)
    os.replace(staged_olean, final_olean)
    os.replace(staged_ilean, final_ilean)
    return 0, result.stdout


def build(target: str, jobs: int, output: Path | None = None) -> tuple[dict[str, str], str]:
    if not 1 <= jobs <= 4:
        raise ValueError("--jobs must be between 1 and 4")
    output = output or ROOT / ".lake/build/lib/lean"
    if not output.is_absolute():
        output = ROOT / output
    output.mkdir(parents=True, exist_ok=True)
    environment, lean, paths = lake_environment(output)
    order, graph, external = dependency_graph(target, paths)
    pending = set(order)
    finished: set[str] = set()
    rank = {module: index for index, module in enumerate(order)}
    skipped = built = 0
    print(f"local import closure: {len(order)} modules; at most {jobs} Lean processes", flush=True)
    with tempfile.TemporaryDirectory(prefix=".build-", dir=output) as temporary:
        staging = Path(temporary)
        with ThreadPoolExecutor(max_workers=jobs) as executor:
            running = {}
            failure: tuple[str, int, str] | None = None
            while pending or running:
                ready = sorted(
                    (module for module in pending if all(dep in finished for dep in graph[module])),
                    key=rank.__getitem__,
                ) if failure is None else []
                for module in ready:
                    if fresh(output, module, graph[module], external[module]):
                        pending.remove(module)
                        finished.add(module)
                        skipped += 1
                    elif len(running) < jobs:
                        pending.remove(module)
                        future = executor.submit(compile_one, module, output, staging,
                                                 environment, lean)
                        running[future] = module
                if running:
                    completed, _ = wait(running, return_when=FIRST_COMPLETED)
                    for future in completed:
                        module = running.pop(future)
                        code, output_text = future.result()
                        if code:
                            failure = failure or (module, code, output_text)
                        else:
                            finished.add(module)
                            built += 1
                            print(f"[{len(finished)}/{len(order)}] compiled {module}", flush=True)
                elif failure is not None:
                    break
                elif not ready and pending:
                    raise RuntimeError("no schedulable module remains")
            if failure is not None:
                module, code, output_text = failure
                raise RuntimeError(f"Lean failed compiling {module} (exit {code}):\n{output_text}")
    print(f"local modules: {built} compiled, {skipped} fresh", flush=True)
    return environment, lean
