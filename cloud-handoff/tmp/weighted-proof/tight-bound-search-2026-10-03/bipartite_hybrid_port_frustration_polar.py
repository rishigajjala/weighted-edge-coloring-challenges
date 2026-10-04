"""Full-profit polar gap for a physical port-reusing bipartite gadget.

Heavy matching: A=(L0,R0), B=(L1,R1), C=(L2,R2).
Four other bundles: A->B, B->C, hub->A, hub->C, where hub is a
fixed left vertex.  One port of C is reused.  Edge weights are integer
hundredths; global count patterns and exact local knapsack patterns
are enumerated. Qhull/HiGHS results are numerical diagnostics.
"""

import itertools
import json
import sys

import numpy as np
from scipy.optimize import linprog
from scipy.spatial import HalfspaceIntersection

EDGES = [(0, 3), (1, 4), (2, 5), (0, 4), (1, 5), (6, 3), (6, 5)]
LEFT = {0, 1, 2, 6}
D = len(EDGES)
NV = 7


def patterns(weights):
    caps = [100 // w for w in weights]
    feasible = []
    maximal = []
    for z in itertools.product(*(range(k + 1) for k in caps)):
        loads = [0] * NV
        for e, (u, v) in enumerate(EDGES):
            loads[u] += weights[e] * z[e]
            loads[v] += weights[e] * z[e]
        if max(loads) > 100:
            continue
        feasible.append(z)
        if not any(loads[u] + weights[e] <= 100 and
                   loads[v] + weights[e] <= 100
                   for e, (u, v) in enumerate(EDGES)):
            maximal.append(z)
    return np.asarray(maximal, dtype=float), len(feasible)


def local_matrix(weights):
    pats = []
    inc = []
    for v in range(NV):
        ids = [e for e, uv in enumerate(EDGES) if v in uv]
        inc.append(ids)
        local = []
        for z in itertools.product(*(range(100 // weights[e] + 1)
                                     for e in ids)):
            if sum(weights[e] * c for e, c in zip(ids, z)) <= 100:
                local.append(z)
        pats.append(local)
    offsets = np.cumsum([0] + [len(p) for p in pats])
    Aeq = np.zeros((NV + D, offsets[-1]))
    b = np.r_[np.ones(NV), np.zeros(D)]
    P = np.zeros((D, offsets[-1]))
    for v in range(NV):
        Aeq[v, offsets[v]:offsets[v + 1]] = 1
        for j, p in enumerate(pats[v]):
            col = offsets[v] + j
            for e, c in zip(inc[v], p):
                if v in LEFT:
                    Aeq[NV + e, col] += c
                    P[e, col] += c
                else:
                    Aeq[NV + e, col] -= c
    return Aeq, b, P, [len(p) for p in pats]


def score(weights):
    G, allcount = patterns(weights)
    Aeq, b, P, loccounts = local_matrix(weights)
    hs = np.vstack((np.c_[G, -np.ones(len(G))],
                    np.c_[-np.eye(D), np.zeros(D)]))
    q0 = np.full(D, 1 / (max(G.sum(axis=1)) + 1))
    V = HalfspaceIntersection(hs, q0, qhull_options="Qx").intersections
    V = np.unique(np.round(V, 10), axis=0)
    best = (0, None, None)
    for q in V:
        lp = linprog(-(q @ P), A_eq=Aeq, b_eq=b,
                     bounds=(0, None), method="highs")
        if not lp.success:
            raise RuntimeError(lp.message)
        val = -lp.fun
        if val > best[0] + 1e-9:
            best = val, q, P @ lp.x
    val, q, x = best
    return dict(weights=weights, feasible_patterns=allcount,
                maximal_patterns=len(G), polar_vertices=len(V),
                local_pattern_counts=loccounts, gap=val,
                profit=np.round(q, 10).tolist(),
                local_point=np.round(x, 10).tolist(),
                global_profit=float(np.max(G @ q)))


if __name__ == "__main__":
    weights = [int(t) for t in sys.argv[1].split(",")]
    assert len(weights) == D and min(weights) > 0 and max(weights) <= 100
    print(json.dumps(score(weights)), flush=True)
