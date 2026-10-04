"""Full-profit polar gap for a fixed multi-rank K3,3 weighted template.

All weights are integer hundredths.  Global repeatable-count patterns
and each exact local knapsack pattern are enumerated.  Polar vertices
are obtained numerically by Qhull; local support values by HiGHS.
Promising results require exact rational re-verification.
"""

import itertools
import json
import sys

import numpy as np
from scipy.optimize import linprog
from scipy.spatial import HalfspaceIntersection

EDGES = [(i, 3 + j) for i in range(3) for j in range(3)]
D = len(EDGES)


def enumerate_patterns(weights):
    lim = [100 // w for w in weights]
    allp = []
    maximal = []
    for z in itertools.product(*(range(k + 1) for k in lim)):
        loads = [0] * 6
        for e, (u, v) in enumerate(EDGES):
            loads[u] += weights[e] * z[e]
            loads[v] += weights[e] * z[e]
        if max(loads) > 100:
            continue
        allp.append(z)
        if not any(loads[u] + weights[e] <= 100 and
                   loads[v] + weights[e] <= 100
                   for e, (u, v) in enumerate(EDGES)):
            maximal.append(z)
    return np.asarray(maximal, dtype=float), len(allp)


def local_lp_matrix(weights):
    pats = []
    inc = []
    for v in range(6):
        ids = [e for e, uv in enumerate(EDGES) if v in uv]
        inc.append(ids)
        local = []
        for zz in itertools.product(*(range(100 // weights[e] + 1)
                                      for e in ids)):
            if sum(weights[e] * k for e, k in zip(ids, zz)) <= 100:
                local.append(zz)
        pats.append(local)
    offsets = np.cumsum([0] + [len(p) for p in pats])
    nvar = offsets[-1]
    Aeq = np.zeros((6 + D, nvar))
    beq = np.r_[np.ones(6), np.zeros(D)]
    profit = np.zeros((D, nvar))
    for v in range(6):
        Aeq[v, offsets[v]:offsets[v + 1]] = 1
        for j, p in enumerate(pats[v]):
            idx = offsets[v] + j
            for e, k in zip(inc[v], p):
                if v < 3:
                    Aeq[6 + e, idx] += k
                    profit[e, idx] += k
                else:
                    Aeq[6 + e, idx] -= k
    return Aeq, beq, profit, [len(p) for p in pats]


def score(weights):
    pp, allcount = enumerate_patterns(weights)
    Aeq, beq, profit, loccounts = local_lp_matrix(weights)
    hs = np.vstack((np.c_[pp, -np.ones(len(pp))],
                    np.c_[-np.eye(D), np.zeros(D)]))
    q0 = np.full(D, 1 / (max(pp.sum(axis=1)) + 1))
    polar = HalfspaceIntersection(hs, q0, qhull_options="Qx")
    vv = np.unique(np.round(polar.intersections, 10), axis=0)
    best = (0, None, None)
    for q in vv:
        c = -(q @ profit)
        lp = linprog(c, A_eq=Aeq, b_eq=beq, bounds=(0, None),
                     method="highs")
        if not lp.success:
            raise RuntimeError(lp.message)
        val = -lp.fun
        if val > best[0] + 1e-9:
            best = val, q, profit @ lp.x
    val, q, x = best
    return dict(weights=weights, feasible_patterns=allcount,
                maximal_patterns=len(pp), polar_vertices=len(vv),
                local_pattern_counts=loccounts, gap=val,
                profit=np.round(q, 10).tolist(),
                local_point=np.round(x, 10).tolist(),
                global_profit=float(np.max(pp @ q)))


if __name__ == "__main__":
    weights = [int(t) for t in sys.argv[1].split(",")]
    assert len(weights) == D and min(weights) > 0 and max(weights) <= 100
    print(json.dumps(score(weights)), flush=True)
