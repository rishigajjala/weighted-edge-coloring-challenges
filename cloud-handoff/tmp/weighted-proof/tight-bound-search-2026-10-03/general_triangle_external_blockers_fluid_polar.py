"""Triangle relation with two external heavy blockers and fluid spokes.

Vertices a,b,c plus private heavy leaves u,v. Unit edge ab, fluid
star ac,bc; heavy au and bv of weights w1,w2. This tests whether the
triangle's positive/negative boundary needs compound a blocker loss.
"""

import json
import sys

import numpy as np
from scipy.optimize import linprog
from scipy.spatial import HalfspaceIntersection


def unique(rows):
    return np.unique(np.round(np.asarray(rows, dtype=float), 12), axis=0)


def local_patterns(w):
    rows = []
    for h in (0, 1):
        for p in (0, 1):
            r = 1 - w * h - p
            if r < -1e-10:
                continue
            for y in (0, max(0, r)):
                rows.append((h, p, y))
    return unique(rows)


def global_patterns(w1, w2):
    rows = []
    for h1 in (0, 1):
        for h2 in (0, 1):
            for p in (0, 1):
                ra = 1 - w1 * h1 - p
                rb = 1 - w2 * h2 - p
                if min(ra, rb) < -1e-10:
                    continue
                ra, rb = max(0, ra), max(0, rb)
                fluids = [(0, 0), (ra, 0), (0, rb)]
                if ra + rb <= 1 + 1e-10:
                    fluids.append((ra, rb))
                else:
                    fluids.extend(((ra, 1 - ra), (1 - rb, rb)))
                for ya, yb in fluids:
                    rows.append((h1, h2, p, ya, yb))
    return unique(rows)


def local_lp_matrix(w1, w2):
    a, b = local_patterns(w1), local_patterns(w2)
    c = unique([(0, 0), (1, 0), (0, 1)])
    pats = [a, b, c]
    offsets = np.cumsum([0] + [len(p) for p in pats])
    Aeq = np.zeros((6, offsets[-1]))
    beq = np.r_[np.ones(3), np.zeros(3)]
    profit = np.zeros((5, offsets[-1]))
    for v in range(3):
        Aeq[v, offsets[v]:offsets[v+1]] = 1
    for j, (h,p,y) in enumerate(a):
        idx=offsets[0]+j
        Aeq[3,idx]+=p;Aeq[4,idx]+=y
        profit[0,idx]+=h;profit[2,idx]+=p;profit[3,idx]+=y
    for j, (h,p,y) in enumerate(b):
        idx=offsets[1]+j
        Aeq[3,idx]-=p;Aeq[5,idx]+=y
        profit[1,idx]+=h;profit[4,idx]+=y
    for j, (ya,yb) in enumerate(c):
        idx=offsets[2]+j
        Aeq[4,idx]-=ya;Aeq[5,idx]-=yb
    return Aeq,beq,profit,[len(p) for p in pats]


def score(w1,w2):
    pp=global_patterns(w1,w2)
    Aeq,beq,profit,nloc=local_lp_matrix(w1,w2)
    hs=np.vstack((np.c_[pp,-np.ones(len(pp))],
                  np.c_[-np.eye(5),np.zeros(5)]))
    q0=np.full(5,1/(max(pp.sum(axis=1))+1))
    polar=HalfspaceIntersection(hs,q0,qhull_options="Qx")
    vv=unique(polar.intersections)
    best=(0,None,None)
    for q in vv:
        lp=linprog(-(q@profit),A_eq=Aeq,b_eq=beq,
                   bounds=(0,None),method="highs")
        if not lp.success:raise RuntimeError(lp.message)
        if -lp.fun>best[0]+1e-9:
            best=(-lp.fun,q,profit@lp.x)
    gap,q,x=best
    return dict(weights=[w1,w2],global_patterns=len(pp),
                polar_vertices=len(vv),local_pattern_counts=nloc,
                gap=gap,profit=np.round(q,8).tolist(),
                local_point=np.round(x,8).tolist(),
                global_profit=float(np.max(pp@q)))


if __name__=="__main__":
    for arg in sys.argv[1:]:
        w1,w2=map(float,arg.split(","))
        assert .5<w1<=1 and .5<w2<=1
        print(json.dumps(score(w1,w2)),flush=True)
