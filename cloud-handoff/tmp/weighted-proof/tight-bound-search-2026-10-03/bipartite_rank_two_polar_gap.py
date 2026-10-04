"""Exact-support numerical polar-vertex gap search for small bipartite templates.

All configurations are enumerated exactly with integer weights. Qhull and
HiGHS are floating point, so promising witnesses require rational auditing.
"""
from __future__ import annotations

import argparse
import itertools
import json
import time

import numpy as np
from scipy.optimize import linprog
from scipy.spatial import HalfspaceIntersection


def patterns(edges, weights, nv):
    out = []
    for z in itertools.product(range(3), repeat=len(edges)):
        loads = [0] * nv
        for (u, v), w, count in zip(edges, weights, z):
            loads[u] += w * count
            loads[v] += w * count
        if max(loads) <= 100:
            out.append(z)
    feasible = set(out)
    maximal = []
    for z in out:
        if not any(
            z[i] < 2 and tuple(z[j] + (j == i) for j in range(len(z))) in feasible
            for i in range(len(z))
        ):
            maximal.append(z)
    return np.array(maximal, dtype=float), len(out)


def local_rows(edges, weights, nv):
    rows = []
    rhs = []
    for v in range(nv):
        inc = [i for i, (a, b) in enumerate(edges) if a == v or b == v]
        heavy = [i for i in inc if weights[i] > 50]
        small = [i for i in inc if weights[i] <= 50]
        row = np.zeros(len(edges))
        row[heavy] = 1
        rows.append(row)
        rhs.append(1)
        for mask in range(1 << len(heavy)):
            xset = [heavy[j] for j in range(len(heavy)) if mask & (1 << j)]
            compatible = {
                i for i in small if any(weights[i] + weights[h] <= 100 for h in xset)
            }
            row = np.zeros(len(edges))
            row[heavy] = 1
            row[xset] += 1
            row[[i for i in small if i not in compatible]] = 1
            rows.append(row)
            rhs.append(2)
    return np.array(rows), np.array(rhs)


def score(edges, weights, nv, *, qhull_options="Qx", limit=0):
    t0 = time.monotonic()
    pp, count = patterns(edges, weights, nv)
    d = len(edges)
    aa, bb = local_rows(edges, weights, nv)
    hs = np.vstack((np.c_[pp, -np.ones(len(pp))], np.c_[-np.eye(d), np.zeros(d)]))
    q0 = np.full(d, 1 / (max(pp.sum(axis=1)) + 1))
    polar = HalfspaceIntersection(hs, q0, qhull_options=qhull_options)
    vv = np.unique(np.round(polar.intersections, 10), axis=0)
    best = (-1, None, None)
    for j, q in enumerate(vv):
        lp = linprog(-q, A_ub=aa, b_ub=bb, bounds=(0, None), method="highs")
        if not lp.success:
            raise RuntimeError(lp.message)
        gap = -lp.fun
        if gap > best[0]:
            best = (gap, q.tolist(), lp.x.tolist())
        if limit and j + 1 >= limit:
            break
    gap, q, x = best
    return dict(weights=weights, edges=edges, feasible_patterns=count,
                maximal_patterns=len(pp), polar_vertices=len(vv),
                evaluated=min(len(vv), limit) if limit else len(vv),
                gap=gap, profit=q, local_point=x,
                global_profit=float(np.max(pp @ q)),
                local_rows=int(len(aa)), elapsed=time.monotonic()-t0)


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--weights", required=True, help="comma-separated integer percent weights")
    ap.add_argument("--template", choices=["k33", "c4double", "pathchord"], default="k33")
    ap.add_argument("--limit", type=int, default=0)
    args = ap.parse_args()
    if args.template == "k33":
        edges = [(i, 3 + j) for i in range(3) for j in range(3)]
        nv = 6
    elif args.template == "c4double":
        edges = [(0, 2), (0, 2), (0, 3), (0, 3),
                 (1, 2), (1, 2), (1, 3), (1, 3)]
        nv = 4
    else:
        edges = [(i,i+1) for i in range(4)] + [(i,5+i) for i in range(5)] + [(0,3)]
        nv = 10
    weights = [int(z) for z in args.weights.split(",")]
    assert len(weights) == len(edges)
    assert min(weights) > 100 / 3 and max(weights) <= 100
    print(json.dumps(score(edges, weights, nv, limit=args.limit)), flush=True)


if __name__ == "__main__":
    main()
