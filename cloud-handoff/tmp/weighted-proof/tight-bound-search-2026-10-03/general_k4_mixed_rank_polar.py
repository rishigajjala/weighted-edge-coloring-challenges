"""Full local/global profit gap for six-type weighted K4 templates.

All weights are integer hundredths. This is a diagnostic, not a proof:
polar vertices and local LPs are floating point and promising cases need
exact verification.
"""

import itertools
import json
import sys

import numpy as np
from scipy.optimize import linprog
from scipy.spatial import HalfspaceIntersection


EDGES = [(0, 1), (0, 2), (1, 2), (0, 3), (1, 3), (2, 3)]
D = len(EDGES)


def patterns(weights):
    lim = [100 // w for w in weights]
    maximal = []
    count = 0
    for z in itertools.product(*(range(k + 1) for k in lim)):
        loads = [0] * 4
        for e, (u, v) in enumerate(EDGES):
            loads[u] += weights[e] * z[e]
            loads[v] += weights[e] * z[e]
        if max(loads) > 100:
            continue
        count += 1
        if not any(loads[u] + weights[e] <= 100 and
                   loads[v] + weights[e] <= 100
                   for e, (u, v) in enumerate(EDGES)):
            maximal.append(z)
    return np.asarray(maximal, dtype=float), count


def local_lp(weights):
    inc = [[e for e, pair in enumerate(EDGES) if v in pair]
           for v in range(4)]
    pats = []
    for v in range(4):
        local = []
        for z in itertools.product(*(range(100 // weights[e] + 1)
                                     for e in inc[v])):
            if sum(weights[e] * k for e, k in zip(inc[v], z)) <= 100:
                local.append(z)
        pats.append(local)
    offsets = np.cumsum([0] + [len(p) for p in pats])
    nvar = offsets[-1]
    Aeq = np.zeros((4 + D, nvar))
    beq = np.r_[np.ones(4), np.zeros(D)]
    profit = np.zeros((D, nvar))
    for v in range(4):
        Aeq[v, offsets[v]:offsets[v + 1]] = 1
        for j, pat in enumerate(pats[v]):
            idx = offsets[v] + j
            for e, k in zip(inc[v], pat):
                u, _ = EDGES[e]
                Aeq[4 + e, idx] += k if v == u else -k
                if v == u:
                    profit[e, idx] += k
    return Aeq, beq, profit, [len(p) for p in pats]


def score(weights):
    p, count = patterns(weights)
    Aeq, beq, profit, nloc = local_lp(weights)
    hs = np.vstack((np.c_[p, -np.ones(len(p))],
                    np.c_[-np.eye(D), np.zeros(D)]))
    q0 = np.full(D, 1 / (max(p.sum(axis=1)) + 1))
    polar = HalfspaceIntersection(hs, q0, qhull_options="Qx")
    vv = np.unique(np.round(polar.intersections, 10), axis=0)
    best = (0, None, None)
    for q in vv:
        lp = linprog(-(q @ profit), A_eq=Aeq, b_eq=beq,
                     bounds=(0, None), method="highs")
        if not lp.success:
            raise RuntimeError(lp.message)
        if -lp.fun > best[0] + 1e-9:
            best = -lp.fun, q, profit @ lp.x
    gap, q, x = best
    return dict(weights=weights, feasible_patterns=count,
                maximal_patterns=len(p), polar_vertices=len(vv),
                local_pattern_counts=nloc, gap=gap,
                profit=np.round(q, 8).tolist(),
                local_point=np.round(x, 8).tolist(),
                global_profit=float(np.max(p @ q)))


if __name__ == "__main__":
    for arg in sys.argv[1:]:
        weights = [int(t) for t in arg.split(",")]
        assert len(weights) == D and min(weights) > 0
        print(json.dumps(score(weights)), flush=True)
