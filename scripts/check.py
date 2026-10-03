#!/usr/bin/env python3
"""Build and axiom-check the exported weighted-edge-coloring proof.

This uses the project's pinned Lake workspace. On a fresh checkout, run with
``--fetch-cache`` (or run ``lake exe cache get`` separately) before building.
No machine-specific Mathlib cache or prebuilt project OLean is required.
"""

from __future__ import annotations

import argparse
import re
import shutil
import subprocess
import sys
import tempfile
from pathlib import Path

from bounded_build import build as bounded_build


ROOT = Path(__file__).resolve().parents[1]
DEFAULT_MODULE = "Verification"
DEFAULT_THEOREMS = (
    "WeightedEdgeColoringChallenge.solve_problem_1",
    "WeightedEdgeColoringChallenge.solve_problem_2",
    "WeightedEdgeColoringChallenge.solve_problem_3",
    "WeightedEdgeColoringChallenge.solve_problem_4",
    "WeightedEdgeColoringChallenge.solve_problem_5",
    "WeightedEdgeColoring.subtwoBPAsymptotic_unrestricted",
)
STANDARD_AXIOMS = frozenset({"propext", "Classical.choice", "Quot.sound"})
LEAN_NAME = re.compile(r"[A-Za-z_][A-Za-z_0-9']*(?:\.[A-Za-z_][A-Za-z_0-9']*)*")


def run(*args: str, capture: bool = False) -> subprocess.CompletedProcess[str]:
    command = ["lake", *args]
    print("+ " + " ".join(command), flush=True)
    return subprocess.run(
        command,
        cwd=ROOT,
        text=True,
        stdout=subprocess.PIPE if capture else None,
        stderr=subprocess.STDOUT if capture else None,
        check=True,
    )


def audit_axioms(module: str, theorems: list[str],
                 environment: dict[str, str] | None = None,
                 lean: str | None = None) -> None:
    for theorem in theorems:
        if not LEAN_NAME.fullmatch(theorem):
            raise ValueError(f"not a Lean constant name: {theorem!r}")
    with tempfile.TemporaryDirectory(prefix="weighted-edge-coloring-check-") as temp:
        check_file = Path(temp) / "CheckAxioms.lean"
        queries = "\n".join(f"#print axioms {theorem}" for theorem in theorems)
        check_file.write_text(f"import {module}\n{queries}\n")
        if environment is None or lean is None:
            result = run("env", "lean", str(check_file), capture=True)
        else:
            command = [lean, str(check_file)]
            print("+ lean " + str(check_file), flush=True)
            result = subprocess.run(command, cwd=ROOT, env=environment,
                                    text=True, stdout=subprocess.PIPE,
                                    stderr=subprocess.STDOUT, check=True)
    output = result.stdout
    print(output, end="" if output.endswith("\n") else "\n")
    for theorem in theorems:
        quoted_theorem = re.escape(theorem)
        pattern = rf"(?:'{quoted_theorem}'|{quoted_theorem})" + (
            r" (?:depends on axioms:\s*\[([^\]]*)\]"
            r"|does not depend on (?:any )?axioms)"
        )
        matches = re.findall(pattern, output)
        if len(matches) != 1:
            raise RuntimeError(f"Lean did not report exactly one axiom set for {theorem}")
        axioms = {name.strip() for name in matches[0].split(",") if name.strip()}
        unexpected = axioms - STANDARD_AXIOMS
        if unexpected:
            raise RuntimeError(f"unexpected axioms in {theorem}: {sorted(unexpected)}")


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--module", default=DEFAULT_MODULE,
                        help=f"module to build (default: {DEFAULT_MODULE})")
    parser.add_argument("--theorem", action="append", dest="theorems",
                        help="constant to axiom-check; repeat to check several (default: all public theorems)")
    parser.add_argument("--fetch-cache", action="store_true",
                        help="download the pinned Mathlib cache before building")
    parser.add_argument("--jobs", type=int, default=None,
                        help="maximum concurrent Lean processes (1–4; default: 3)")
    parser.add_argument("--lake-build", action="store_true",
                        help="use Lake's normal build scheduler instead of bounded source compilation")
    parser.add_argument("--skip-axioms", action="store_true",
                        help="build only, without the final theorem axiom check")
    args = parser.parse_args()

    if not LEAN_NAME.fullmatch(args.module):
        parser.error(f"not a Lean module name: {args.module!r}")
    if args.lake_build and args.jobs is not None:
        parser.error("--jobs cannot be combined with --lake-build")
    if args.jobs is not None and not 1 <= args.jobs <= 4:
        parser.error("--jobs must be between 1 and 4")
    if shutil.which("lake") is None:
        parser.error("Lake is unavailable; install Elan and the pinned Lean toolchain")

    try:
        if args.fetch_cache:
            run("exe", "cache", "get")
        if args.lake_build:
            run("build", "+" + args.module)
            environment = lean = None
        else:
            environment, lean = bounded_build(args.module, args.jobs or 3)
        if not args.skip_axioms:
            audit_axioms(args.module, list(dict.fromkeys(args.theorems or DEFAULT_THEOREMS)),
                         environment, lean)
    except (OSError, subprocess.CalledProcessError, RuntimeError, ValueError) as error:
        print(f"verification failed: {error}", file=sys.stderr)
        return 1
    print("verification passed", flush=True)
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
