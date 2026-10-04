"""Full nonnegative-profit gap on a four-vertex discrete/fluid diamond.

Vertices a,b,c,d. Discrete unit base ab, medium spokes ca,cb of size s;
divisible fluid da,db. A color pattern records (base,ca,cb,da,db).
"""

import json
import sys

import numpy as np
from scipy.optimize import linprog
from scipy.spatial import HalfspaceIntersection


def unique(rows):
    return np.unique(np.round(np.asarray(rows, dtype=float), 12), axis=0)


def local_patterns(h, s):
    k = int(np.floor((1 + 1e-10) / s))
    at_ab = []
    for e in (0, 1):
        for f in range(k + 1):
            residual = 1 - h * e - s * f
            if residual < -1e-10:
                continue
            for y in (0, max(residual, 0)):
                at_ab.append((e, f, y))
    at_c = [(fa, fb) for fa in range(k + 1)
            for fb in range(k + 1) if s * (fa + fb) <= 1 + 1e-10]
    at_d = [(0, 0), (1, 0), (0, 1)]
    return unique(at_ab), unique(at_c), unique(at_d)


def global_patterns(h, s):
    k = int(np.floor((1 + 1e-10) / s))
    out = []
    for e in (0, 1):
        for fa in range(k + 1):
            for fb in range(k + 1):
                if h * e + s * fa > 1 + 1e-10 or h * e + s * fb > 1 + 1e-10:
                    continue
                if s * (fa + fb) > 1 + 1e-10:
                    continue
                ra = max(0, 1 - h * e - s * fa)
                rb = max(0, 1 - h * e - s * fb)
                fluids = [(0, 0), (ra, 0), (0, rb)]
                if ra + rb <= 1 + 1e-10:
                    fluids.append((ra, rb))
                else:
                    fluids.extend(((ra, 1 - ra), (1 - rb, rb)))
                for ya, yb in fluids:
                    out.append((e, fa, fb, ya, yb))
    return unique(out)


def local_lp_matrix(h, s):
    ab, c, d = local_patterns(h, s)
    pats = [ab, ab, c, d]
    offsets = np.cumsum([0] + [len(p) for p in pats])
    nvar = offsets[-1]
    # 4 normalizations and 5 edge-type consistency constraints.
    Aeq = np.zeros((9, nvar))
    beq = np.r_[np.ones(4), np.zeros(5)]
    profit = np.zeros((5, nvar))
    for v in range(4):
        Aeq[v, offsets[v]:offsets[v + 1]] = 1
    for j, (e, fa, ya) in enumerate(ab):
        idx = offsets[0] + j
        Aeq[4, idx] += e; Aeq[5, idx] += fa; Aeq[7, idx] += ya
        profit[0, idx] += e; profit[1, idx] += fa; profit[3, idx] += ya
    for j, (e, fb, yb) in enumerate(ab):
        idx = offsets[1] + j
        Aeq[4, idx] -= e; Aeq[6, idx] += fb; Aeq[8, idx] += yb
        profit[2, idx] += fb; profit[4, idx] += yb
    for j, (fa, fb) in enumerate(c):
        idx = offsets[2] + j
        Aeq[5, idx] -= fa; Aeq[6, idx] -= fb
    for j, (ya, yb) in enumerate(d):
        idx = offsets[3] + j
        Aeq[7, idx] -= ya; Aeq[8, idx] -= yb
    return Aeq, beq, profit, [len(p) for p in pats]


def score(h, s):
    patterns = global_patterns(h, s)
    Aeq, beq, profit, nloc = local_lp_matrix(h, s)
    hs = np.vstack((np.c_[patterns, -np.ones(len(patterns))],
                    np.c_[-np.eye(5), np.zeros(5)]))
    q0 = np.full(5, 1 / (max(patterns.sum(axis=1)) + 1))
    polar = HalfspaceIntersection(hs, q0, qhull_options="Qx")
    vv = unique(polar.intersections)
    best = (0, None, None)
    for q in vv:
        lp = linprog(-(q @ profit), A_eq=Aeq, b_eq=beq,
                     bounds=(0, None), method="highs")
        if not lp.success:
            raise RuntimeError(lp.message)
        if -lp.fun > best[0] + 1e-9:
            best = -lp.fun, q, profit @ lp.x
    gap, q, x = best
    return dict(heavy_size=h, spoke_size=s, global_patterns=len(patterns),
                polar_vertices=len(vv), local_pattern_counts=nloc,
                gap=gap, profit=np.round(q, 8).tolist(),
                local_point=np.round(x, 8).tolist(),
                global_profit=float(np.max(patterns @ q)))


if __name__ == "__main__":
    for arg in sys.argv[1:]:
        if "," in arg:
            h, s = map(float, arg.split(","))
        else:
            h, s = 1.0, float(arg)
        assert 0.5 < h <= 1 and 0 < s <= 1
        print(json.dumps(score(h, s)), flush=True)
