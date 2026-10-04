"""Exploratory support-function check for bipartite heavy path of length three.

Compares the exact one-color global mixed optimum with 3/4 times the exact
local heavy-categorical + fluid LP optimum. A sample is only evidence.
"""

from __future__ import annotations

import random
import numpy as np
from scipy.optimize import linprog


ALPHA = 0.75
V = 6
LEFT = (0, 2, 4)
RIGHT = (1, 3, 5)
HEAVY = ((0, 1), (2, 1), (2, 3))
STATES = ((), (0,), (1,), (2,), (0, 2))
FLUID_POOL = tuple((u, v) for u in LEFT for v in RIGHT)


def matrix(edges):
    a = np.zeros((V, len(edges)))
    for k, (u, v) in enumerate(edges):
        a[u, k] = a[v, k] = 1
    return a


def compare(edges, h, cheavy, qfluid):
    ah = matrix(HEAVY)
    af = matrix(edges)
    h = np.asarray(h)
    ch = np.asarray(cheavy)
    q = np.asarray(qfluid)
    n = len(edges)
    # Local LP: categorical heavy degree and mean weighted load at each vertex.
    c = np.r_[ch, q]
    bounds = [(0, None)] * (3 + n)
    a1 = np.column_stack((ah, np.zeros((V, n))))
    a2 = np.column_stack((ah * h, af))
    sol = linprog(-c, A_ub=np.vstack((a1, a2)), b_ub=np.ones(2 * V),
                  bounds=bounds, method="highs")
    if not sol.success:
        raise RuntimeError(sol.message)
    local = -sol.fun
    best_state = None
    global_opt = -1
    for state in STATES:
        residual = np.ones(V)
        for i in state:
            u, v = HEAVY[i]
            residual[u] -= h[i]
            residual[v] -= h[i]
        f = linprog(-q, A_ub=af, b_ub=residual,
                    bounds=(0, None), method="highs")
        if not f.success:
            raise RuntimeError(f.message)
        val = sum(ch[i] for i in state) - f.fun
        if val > global_opt:
            global_opt = val
            best_state = state
    return global_opt - ALPHA * local, local, global_opt, sol.x, best_state


def main():
    rng = random.Random(20261003)
    best = (float("inf"), None)
    for trial in range(25000):
        edges = tuple(e for e in FLUID_POOL if rng.random() < 0.5)
        if not edges:
            continue
        h = tuple(rng.choice((0.51, 0.6, 0.75, 0.9, 1.0)) for _ in HEAVY)
        ch = tuple(rng.choice((0.05, 0.1, 0.25, 0.5, 1, 2, 4)) for _ in HEAVY)
        q = tuple(rng.choice((0.05, 0.1, 0.25, 0.5, 1, 2, 4)) for _ in edges)
        gap, local, glob, point, state = compare(edges, h, ch, q)
        ratio = glob / local if local else 1
        if ratio < best[0]:
            best = (ratio, (trial, gap, edges, h, ch, q, local, glob, point, state))
            print("best", best, flush=True)
            if gap < -1e-8:
                break
    print("final", best)


if __name__ == "__main__":
    main()
