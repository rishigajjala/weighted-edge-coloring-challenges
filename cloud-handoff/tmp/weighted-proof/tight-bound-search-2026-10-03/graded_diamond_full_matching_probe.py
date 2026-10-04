"""Targeted source-sink diamond, a genuine non-tree core with rank 2 -> 3.

The guard counts match every outgoing core edge at source and side vertices;
the sink guards reject both incoming rank-three bundles. Each LP is the
asymptotic repeatable-count covering relaxation for this *fixed* template.
The output is a diagnostic, not a finite physical-edge certificate.
"""

import itertools
import numpy as np
from scipy.optimize import linprog

W = (.4, .4, .3, .3)
H = (.6, .7, .7, 1.0)
END = ((0, 1), (0, 2), (1, 3), (2, 3))
K = (2, 2, 3, 3)

states = []
for core in itertools.product(*(range(k + 1) for k in K)):
    for guard in itertools.product((0, 1), repeat=4):
        load = [H[v] * guard[v] for v in range(4)]
        for e, (u, v) in enumerate(END):
            load[u] += W[e] * core[e]
            load[v] += W[e] * core[e]
        if max(load) <= 1 + 1e-9:
            states.append(core + guard)
P = np.asarray(states, dtype=float).T
print('global patterns', P.shape[1], flush=True)

def cover(d):
    result = linprog(np.ones(P.shape[1]), A_ub=-P, b_ub=-np.asarray(d),
                     bounds=(0, None), method='highs')
    if not result.success:
        raise RuntimeError(result.message)
    return result.fun

def bp(d):
    a, b, c, e, gs, gu, gv, gt = d
    assert 0 <= gs <= a+b and 0 <= gu <= c and 0 <= gv <= e
    # Continuous local configuration costs, appropriate for the repeatable
    # asymptotic LP. At a side, residual .4/.3 cores use (2,0),(1,2),(0,3).
    source=gs+(a+b-gs)/2
    side_u=gu+max((a+c-gu)/3, a/2+(c-gu)/4)
    side_v=gv+max((b+e-gv)/3, b/2+(e-gv)/4)
    sink=gt+(c+e)/3
    return max(source, side_u, side_v, sink)

best = (0, None)
tuples = sorted(set(
    (a, b, c, e)
    for a in (1, 2, 3, 4, 5, 6)
    for b in (1, 2, 3, 4, 5, 6)
    for c in (max(1,a//2), a, min(6, 2*a))
    for e in (max(1,b//2), b, min(6, 2*b))
))
for a,b,c,e in tuples:
    for gs in sorted(set((0, (a+b)//2, a+b))):
      for gu in sorted(set((0, c//2, c))):
       for gv in sorted(set((0, e//2, e))):
        d0=(a,b,c,e,gs,gu,gv,0)
        B0=bp(d0)
        hbal=max(0,round(B0-(c+e)/3))
        for h in sorted(set((0,hbal,hbal+1,a+b))):
            d=(a,b,c,e,gs,gu,gv,h)
            B=bp(d)
            G=cover(d)
            ratio=G/B
            if ratio>best[0]+1e-9:
                best=(ratio,(d,B,G))
                print('best',best,flush=True)
print('FINAL',best, 'demand profiles', len(tuples), flush=True)
