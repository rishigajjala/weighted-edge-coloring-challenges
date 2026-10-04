"""Complete-profit numerical gap test for two mixed and four pure stars.

Integer pattern enumeration is exact. Hull/LP arithmetic is floating point;
this is a diagnostic, not a theorem certificate.
"""
import itertools
import json
import time

import numpy as np
from scipy.optimize import linprog
from scipy.spatial import HalfspaceIntersection


def score(weights, capacity=1000):
    t0 = time.monotonic()
    k = np.array([capacity // w for w in weights])
    patterns = np.array([a for a in itertools.product(*(range(int(q)+1) for q in k))
                         if sum(w*j for w,j in zip(weights,a)) <= capacity], dtype=int)
    global_patterns = np.array([np.r_[a,b] for a in patterns for b in patterns
                                if np.all(a+b <= k)], dtype=int)
    # A global pattern is maximal iff no single coordinate can be increased.
    support = set(map(tuple, global_patterns))
    maximal = []
    for z in global_patterns:
        if all(tuple(z + np.eye(2*len(k), dtype=int)[i]) not in support
               for i in range(2*len(k))):
            maximal.append(z)
    maximal = np.array(maximal)
    dim = 2*len(k)
    hs = np.vstack([np.c_[maximal, -np.ones(len(maximal))],
                    np.c_[-np.eye(dim), np.zeros(dim)]])
    interior = np.full(dim, 1/(max(maximal.sum(axis=1))+1))
    vertices = HalfspaceIntersection(hs, interior).intersections
    vertices = np.unique(np.round(vertices, 10), axis=0)
    n = len(patterns)
    eq = np.zeros((2,2*n))
    eq[0,:n] = 1
    eq[1,n:] = 1
    right_caps = np.c_[patterns.T, patterns.T]
    best = None
    for q in vertices:
        profits = np.r_[patterns @ q[:len(k)], patterns @ q[len(k):]]
        lp = linprog(-profits, A_eq=eq, b_eq=np.ones(2), A_ub=right_caps,
                     b_ub=k, bounds=(0,None), method='highs')
        assert lp.success, lp.message
        if best is None or -lp.fun > best['gap']:
            x = np.r_[lp.x[:n] @ patterns, lp.x[n:] @ patterns]
            best = dict(gap=-lp.fun, profits=q.tolist(), local_point=x.tolist(),
                        global_profit=float(np.max(global_patterns @ q)),
                        local_mixtures=[[(patterns[i].tolist(), float(lp.x[j*n+i]))
                                         for i in range(n) if lp.x[j*n+i]>1e-9]
                                        for j in range(2)])
    return dict(weights=weights, pure_capacities=k.tolist(),
                local_patterns=len(patterns), global_patterns=len(global_patterns),
                maximal_patterns=len(maximal), polar_vertices=len(vertices),
                elapsed=time.monotonic()-t0, **best)


if __name__ == '__main__':
    cases = [[501,334,251,167], [600,340,260,200], [501,334,251,143],
             [600,334,251,167], [501,400,260,200], [501,334,200,125],
             [501,334,251,125], [501,334,167,143]]
    for weights in cases:
        print(json.dumps(score(weights)), flush=True)
