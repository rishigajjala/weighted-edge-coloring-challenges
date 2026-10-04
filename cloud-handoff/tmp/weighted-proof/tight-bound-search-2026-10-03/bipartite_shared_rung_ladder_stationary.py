"""Stationary local/global gap for a ladder with shared rung guards.

Each rung guard is incident to both paths, so one physical guard source
simultaneously enforces the descending incompatibility on the two rails.
The rail bundles have rank 2. This differs from independent guard types.
"""

import itertools
import json
import os
import numpy as np
from scipy.optimize import linprog

if os.environ.get('RESONANT_LADDER'):
    CAP = 12000
    AIN, AOUT = 5762, 5760
    BIN, BOUT = 2881, 2880
    GUARD = 6240
else:
    CAP = 6000
    AIN = BIN = 2501
    AOUT = BOUT = 2500
    GUARD = CAP - AOUT
NODES = [(a, b) for a in range(CAP//AOUT+1) for b in range(CAP//BOUT+1)]
NODE_INDEX = {v: i for i, v in enumerate(NODES)}
STATES = []
for ai, bi, ao, bo, g in itertools.product(range(CAP//AOUT+1), range(CAP//BOUT+1),
                                           range(CAP//AOUT+1), range(CAP//BOUT+1), range(2)):
    if AIN*ai + AOUT*ao + GUARD*g <= CAP and BIN*bi + BOUT*bo + GUARD*g <= CAP:
        STATES.append((ai, bi, ao, bo, g))
P = np.array([[s[2], s[3], s[4]] for s in STATES], float)
LOCAL_EQ = np.vstack([
    np.ones(len(STATES)),
    np.array([s[0]-s[2] for s in STATES], float),
    np.array([s[1]-s[3] for s in STATES], float),
])
LOCAL_RHS = np.array([1, 0, 0], float)


def local_vertices():
    out = {}
    for k in (1, 2, 3):
        for support in itertools.combinations(range(len(STATES)), k):
            a = LOCAL_EQ[:, support]
            if np.linalg.matrix_rank(a, tol=1e-9) < k:
                continue
            lam = np.linalg.lstsq(a, LOCAL_RHS, rcond=None)[0]
            if np.max(np.abs(a @ lam-LOCAL_RHS)) > 1e-9 or min(lam) < -1e-9:
                continue
            x = lam @ P[list(support), :]
            out.setdefault(tuple(np.round(x, 10)), (x, support, lam))
    return list(out.values())


def gauge(x, reverse_b=False):
    a = np.zeros((len(STATES), 3+len(NODES)-1))
    a[:, :3] = P
    for j,s in enumerate(STATES):
        src = NODE_INDEX[(s[0], s[3] if reverse_b else s[1])]
        dst = NODE_INDEX[(s[2], s[1] if reverse_b else s[3])]
        if src:
            a[j, 3+src-1] -= 1
        if dst:
            a[j, 3+dst-1] += 1
    c = np.zeros(a.shape[1]); c[:3] = -x
    r = linprog(c, A_ub=a, b_ub=np.ones(len(STATES)),
                bounds=[(0,None)]*3+[(None,None)]*(len(NODES)-1), method='highs')
    if not r.success:
        raise RuntimeError(r.message)
    return -r.fun, r.x[:3]


def main():
    vertices = local_vertices()
    for reverse_b in (False, True):
        best = (0,None)
        for x,support,lam in vertices:
            ratio,p = gauge(x,reverse_b)
            if ratio > best[0]+1e-8:
                best = (ratio, dict(ratio=ratio, profit=p.tolist(),
                                    local_mean=x.tolist(),
                                    support=[(STATES[j],float(t)) for j,t in zip(support,lam)]))
                print('BEST',reverse_b,json.dumps(best[1]),flush=True)
        print('FINAL',json.dumps(dict(reverse_b=reverse_b,states=len(STATES),
                                      vertices=len(vertices),best=best[1])),flush=True)


if __name__=='__main__':
    main()
