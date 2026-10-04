"""Targeted stationary diagnostic: rank-2 and rank-3 descending paths.

The A guard fits one outgoing A item. The B guard fits two outgoing B
items but not two incoming B items. The test checks whether this coupled
rank hierarchy has a local/stationary global gap above 4/3.
"""

import json
import os
import numpy as np
from scipy.optimize import linprog

CAP = 6000
AIN, AOUT, BIN, BOUT = map(int, os.environ.get(
    "MIXED_RANK_WEIGHTS", "2501,2500,1601,1600").split(","))
GA, GB = CAP - AOUT, CAP - 2 * BOUT
NODES = [(a, b) for a in range(3) for b in range(4)]
NODE_INDEX = {v: i for i, v in enumerate(NODES)}

STATES = []
for ai, bi in NODES:
    for ao, bo in NODES:
        for ga in range(2):
            for gb in range(3):
                load = AIN * ai + BIN * bi + AOUT * ao + BOUT * bo + GA * ga + GB * gb
                if load <= CAP:
                    STATES.append((ai, bi, ao, bo, ga, gb))

P = np.array([[s[2], s[3], s[4], s[5]] for s in STATES], dtype=float)
LOCAL_EQ = np.vstack([
    np.ones(len(STATES)),
    np.array([s[0] - s[2] for s in STATES], dtype=float),
    np.array([s[1] - s[3] for s in STATES], dtype=float),
])
LOCAL_RHS = np.array([1, 0, 0], dtype=float)
FLOW_EQ = np.zeros((len(NODES) + 1, len(STATES)), dtype=float)
FLOW_EQ[0, :] = 1
for j, s in enumerate(STATES):
    FLOW_EQ[1 + NODE_INDEX[(s[0], s[1])], j] += 1
    FLOW_EQ[1 + NODE_INDEX[(s[2], s[3])], j] -= 1
FLOW_RHS = np.zeros(len(NODES) + 1)
FLOW_RHS[0] = 1


def values(profit):
    reward = P @ profit
    loc = linprog(-reward, A_eq=LOCAL_EQ, b_eq=LOCAL_RHS,
                  bounds=(0, None), method="highs")
    glob = linprog(-reward, A_eq=FLOW_EQ, b_eq=FLOW_RHS,
                   bounds=(0, None), method="highs")
    if not loc.success or not glob.success:
        raise RuntimeError((loc.message, glob.message))
    return -loc.fun, -glob.fun, loc.x, glob.x


def main():
    print("MODEL", json.dumps({"weights": [AIN, AOUT, BIN, BOUT, GA, GB],
                               "nodes": len(NODES), "states": len(STATES)}), flush=True)
    rng = np.random.default_rng(2026100307)
    best = (1.0, None)
    for it in range(2500):
        profit = np.exp(rng.uniform(-4, 4, size=4))
        if it % 5 == 0:
            profit[rng.integers(0, 4)] = 0
        loc, glob, lx, gx = values(profit)
        ratio = loc / glob if glob else 1
        if ratio > best[0] + 1e-7:
            best = (ratio, {"iteration": it, "ratio": ratio,
                            "profit": profit.tolist(),
                            "local_value": loc, "global_value": glob,
                            "local_support": [(STATES[i], float(x)) for i, x in enumerate(lx) if x > 1e-7],
                            "global_support": [(STATES[i], float(x)) for i, x in enumerate(gx) if x > 1e-7]})
            print("BEST", json.dumps(best[1]), flush=True)
        if it % 250 == 0:
            print("PROGRESS", it, best[0], flush=True)
    print("FINAL", json.dumps(best[1]), flush=True)


if __name__ == "__main__":
    main()
