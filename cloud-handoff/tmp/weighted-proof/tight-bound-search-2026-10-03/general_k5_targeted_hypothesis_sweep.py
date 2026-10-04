"""Finite-weight falsification attempt for a universal K5 3/2 cap.

The weights are assigned independently to all ten K5 edges; templates
are identified under all 120 vertex permutations. Full profit polars
are solved for each canonical template.
"""

import itertools
import json
import sys
import time

import general_k5_cycle_chords_polar as k5

core = k5.core
AUT = list(itertools.permutations(range(core.NV)))
PERM_INDICES = []
for perm in AUT:
    renamed = [tuple(sorted((perm[u], perm[v]))) for u, v in core.EDGES]
    idx = [renamed.index(tuple(sorted(e))) for e in core.EDGES]
    PERM_INDICES.append(idx)


def canonical(weights):
    return min(tuple(weights[j] for j in idx) for idx in PERM_INDICES)


def main(alphabet):
    start = time.time()
    seen = set()
    orbits = 0
    best = (0, None)
    for weights in itertools.product(alphabet, repeat=core.D):
        if weights in seen:
            continue
        images = [tuple(weights[j] for j in idx) for idx in PERM_INDICES]
        seen.update(images)
        orbits += 1
        can = min(images)
        result = core.score(can)
        if result["gap"] > best[0] + 1e-8:
            best = result["gap"], result
            print(json.dumps({"event": "best", "orbits": orbits,
                              "elapsed": time.time() - start,
                              "result": result}), flush=True)
        if result["gap"] > 1.5000001:
            print(json.dumps({"event": "counterexample", "result": result}),
                  flush=True)
            break
        if orbits % 200 == 0:
            print(json.dumps({"event": "progress", "orbits": orbits,
                              "elapsed": time.time() - start}), flush=True)
    print(json.dumps({"event": "done", "alphabet": alphabet,
                      "orbits": orbits, "elapsed": time.time() - start,
                      "max_gap": best[0]}), flush=True)


if __name__ == "__main__":
    main([int(a) for a in sys.argv[1:]])
