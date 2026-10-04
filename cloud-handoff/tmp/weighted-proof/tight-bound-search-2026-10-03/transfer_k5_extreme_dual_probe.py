"""Exact-LP cutting-plane gap probe for the K5 heavy/fluid odd-cycle extreme."""
import itertools
import json
from pathlib import Path

import numpy as np
from scipy.optimize import linprog

N = 5
H = [(i, (i + 1) % 5) for i in range(5)]
F = [(i, (i + 2) % 5) for i in range(5)]
INC_H = np.array([[int(v in e) for e in H] for v in range(N)], dtype=float)
INC_F = np.array([[int(v in e) for e in F] for v in range(N)], dtype=float)
MATCHINGS = []
for bits in itertools.product((0, 1), repeat=5):
    if np.max(INC_H @ bits) <= 1:
        MATCHINGS.append(np.array(bits, dtype=float))


def test(weight, tolerance=1e-9):
    weight = np.array(weight)
    x = np.ones(5) / 2
    residual = np.ones(5) - INC_H @ (weight * x)
    y = np.linalg.solve(INC_F, residual)
    if np.min(y) < -1e-9:
        return None
    target = np.r_[x, y]
    cuts = []
    for i in range(10):
        row = np.zeros(10)
        row[i] = 1
        cuts.append(row)
    for iteration in range(300):
        master = linprog(-target, A_ub=np.array(cuts), b_ub=np.ones(len(cuts)),
                         bounds=(0, None), method="highs")
        if not master.success:
            raise RuntimeError(master.message)
        p, q = master.x[:5], master.x[5:]
        best_value, best_cut = -1, None
        for M in MATCHINGS:
            cap = np.ones(5) - INC_H @ (weight * M)
            sub = linprog(-q, A_ub=INC_F, b_ub=cap, bounds=(0, None), method="highs")
            if not sub.success:
                raise RuntimeError(sub.message)
            value = p @ M - sub.fun
            if value > best_value:
                best_value, best_cut = value, np.r_[M, sub.x]
        if best_value <= 1 + tolerance:
            return dict(ratio=float(-master.fun), weight=weight.tolist(),
                        local_point=target.tolist(), prices=master.x.tolist(),
                        patterns=len(cuts), iterations=iteration + 1,
                        global_check=float(best_value))
        if any(np.max(np.abs(old - best_cut)) < 1e-10 for old in cuts):
            raise RuntimeError("duplicate violated cut")
        cuts.append(best_cut)
    raise RuntimeError("cutting plane did not converge")


def run():
    rng = np.random.default_rng(834120)
    best = None
    count = 0
    for w in [.50001, .55, .6, 2 / 3, .75, .85, .95, 1.0]:
        result = test([w] * 5)
        count += 1
        print("uniform", w, result["ratio"], flush=True)
        if best is None or result["ratio"] > best["ratio"]:
            best = result
    for i in range(2000):
        w = rng.choice([.50001, .55, .6, 2 / 3, .75, .85, .95, 1.0], size=5)
        result = test(w)
        if result is None:
            continue
        count += 1
        if result["ratio"] > best["ratio"]:
            best = result
            print("new best", i, best["ratio"], flush=True)
            if best["ratio"] > 1.50000001:
                break
    out = Path(__file__).with_suffix(".json")
    out.write_text(json.dumps(dict(count=count, best=best), indent=2))
    print("DONE", count, "best", best["ratio"], out, flush=True)


if __name__ == "__main__":
    run()
