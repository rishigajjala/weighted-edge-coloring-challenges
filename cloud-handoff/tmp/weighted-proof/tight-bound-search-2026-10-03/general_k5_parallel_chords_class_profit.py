"""Targeted class-profit search for the 12-type graded K5 gadget."""

import itertools
import json
import sys

import numpy as np
from scipy.optimize import linprog

import general_k5_parallel_chords_polar as model

core = model.core


def main(weights, Q):
    pats, nall = core.patterns(weights)
    Aeq, beq, profit, nloc = core.local_lp(weights)
    print(json.dumps({"event": "enumerated", "patterns": nall,
                      "maximal": len(pats), "local": nloc}), flush=True)
    best = (0, None, None, None)
    for h, m, t in itertools.product(range(Q + 1), repeat=3):
        if h + m + t == 0:
            continue
        q = np.array([h] * 5 + [m] * 5 + [t] * 2)
        g = max(pats @ q)
        lp = linprog(-(q @ profit), A_eq=Aeq, b_eq=beq,
                     bounds=(0, None), method="highs")
        if not lp.success:
            raise RuntimeError(lp.message)
        ratio = -lp.fun / g
        if ratio > best[0] + 1e-9:
            best = ratio, q.tolist(), (profit @ lp.x).tolist(), g
    print(json.dumps({"event": "best", "ratio": best[0],
                      "profit": best[1], "local_point": best[2],
                      "global_profit": best[3]}), flush=True)


if __name__ == "__main__":
    weights = [int(t) for t in sys.argv[1].split(",")]
    Q = int(sys.argv[2])
    main(weights, Q)
