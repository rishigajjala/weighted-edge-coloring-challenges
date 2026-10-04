"""Sweep weight-order templates, optimizing each support over all polar vertices."""
import json
import sys
import time
from pathlib import Path

import numpy as np

HERE = Path(__file__).resolve().parent
sys.path.insert(0, str(HERE))
from bipartite_rank_two_polar_gap import score


def run(template, count, seed):
    rng = np.random.default_rng(seed)
    if template == "k33":
        edges = [(i, 3+j) for i in range(3) for j in range(3)]
        nv = 6
    elif template == "c4double":
        edges = [(0,2),(0,2),(0,3),(0,3),(1,2),(1,2),(1,3),(1,3)]
        nv = 4
    else:
        edges = [(i,i+1) for i in range(4)] + [(i,5+i) for i in range(5)] + [(0,3)]
        nv = 10
    alphabet = np.array([35,38,42,46,49,52,56,60,64,68])
    best = {"gap": 1.0}
    t0 = time.monotonic()
    cases = 0
    failures = 0
    for it in range(count):
        if template == "pathchord" and it % 2 == 0:
            small = [int(w) for w in sorted(rng.choice([35,38,41,44,47,49], size=4, replace=False), reverse=True)]
            weights = small + [100-w for w in small] + [int(rng.choice([55,60,65,75,100]))]
            weights += [int(rng.choice(alphabet))]
        elif it % 3 == 0:
            weights = rng.choice(alphabet, size=len(edges)).tolist()
        elif it % 3 == 1:
            # complementary edge-pairs, often locally close to saturation
            small = rng.choice([35,38,42,46,49], size=len(edges)).tolist()
            weights = [w if rng.random() < .5 else 100-w for w in small]
        else:
            # all four genuine compatibility ranks represented
            weights = rng.choice([36,44,56,64], size=len(edges)).tolist()
        try:
            result = score(edges, weights, nv)
        except Exception as exc:
            failures += 1
            print(json.dumps({"error": str(exc), "weights": weights}), flush=True)
            continue
        cases += 1
        if result["gap"] > best["gap"] + 1e-8:
            best = result
            print("BEST", json.dumps({"case": it, **best}), flush=True)
        if it % 50 == 0:
            print("PROGRESS", json.dumps({"case": it, "best": best["gap"],
                                          "elapsed": time.monotonic()-t0}), flush=True)
        if best["gap"] > 4/3 + 1e-6:
            break
    print("FINAL", json.dumps({"tested": cases, "failures": failures,
                                "best": best, "elapsed": time.monotonic()-t0}), flush=True)


if __name__ == "__main__":
    run(sys.argv[1], int(sys.argv[2]), int(sys.argv[3]))
