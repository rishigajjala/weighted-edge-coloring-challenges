"""Test the conjectured 3/2 K4 cap across all alphabet assignments.

This is a targeted falsification attempt, not evidence of a universal
bound beyond the finite tested alphabets.
"""

import itertools
import json
import sys
import time

import general_k4_mixed_rank_polar as k4


def canonical(weights):
    opts = []
    for perm in itertools.permutations(range(4)):
        renamed = {tuple(sorted((perm[u], perm[v]))): weights[e]
                   for e, (u, v) in enumerate(k4.EDGES)}
        opts.append(tuple(renamed[e] for e in k4.EDGES))
    return min(opts)


def main(alphabet):
    start = time.time()
    seen = set()
    best = (0, None)
    for weights in itertools.product(alphabet, repeat=6):
        can = canonical(weights)
        if can in seen:
            continue
        seen.add(can)
        result = k4.score(can)
        if result["gap"] > best[0] + 1e-8:
            best = result["gap"], result
            print(json.dumps({"event": "best", "orbits": len(seen),
                              "elapsed": time.time() - start,
                              "result": result}), flush=True)
        if result["gap"] > 1.5000001:
            print(json.dumps({"event": "counterexample", "result": result}),
                  flush=True)
            break
    print(json.dumps({"event": "done", "alphabet": alphabet,
                      "orbits": len(seen), "elapsed": time.time() - start,
                      "max_gap": best[0]}), flush=True)


if __name__ == "__main__":
    main([int(a) for a in sys.argv[1:]])
