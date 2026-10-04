"""Four mixed-rank factors with degree-two blocker ports, exact pricing.

Each factor has three spoke bundles: 2×.42 (profit .55 each),
3×.31 (profit .35), 3×.26 (profit .30). Hub local pattern takes
one of each, profit 1.20. Each port locally alternates the one-spoke
marginal with a unit blocker, so with two blockers per port each A
blocker has marginal 1/4 and each B/C blocker marginal 1/3.

Two factor hubs on each bipartition side. Blockers form two perfect
matchings within A ports and within B/C ports; enumerate all 48
topologies, every physical blocker matching, and all nonnegative
blocker profits for this fixed vertex-local point.
"""
import itertools
import numpy as np
from scipy.optimize import linprog

W = np.array([.42, .31, .26])
Q = np.array([.55, .35, .30])
C = [2, 3, 3]
F = np.zeros(8)
for blocked in range(8):
    for counts in itertools.product(*(range(c+1) for c in C)):
        if any(counts[i] and ((blocked>>i)&1) for i in range(3)):
            continue
        if np.dot(W, counts) <= 1+1e-9:
            F[blocked] = max(F[blocked], np.dot(Q, counts))

BITS = ((np.arange(1<<12)[:,None] >> np.arange(12)) & 1).astype(np.uint8)
best = (0., None)
for ap in itertools.permutations(range(2)):
    for bp in itertools.permutations(range(4)):
        # Ports on each shore: F0/F1 use A,B,C at 0,1,2;
        # F2/F3 use A,B,C at 3,4,5.
        leftA = [0,3]
        leftBC = [1,2,4,5]
        rightA = [0,3]
        rightBC = [1,2,4,5]
        left = leftA+leftA+leftBC+leftBC
        right = rightA+[rightA[i] for i in ap]
        right += rightBC+[rightBC[i] for i in bp]
        ok = np.ones(len(BITS), dtype=bool)
        for port in range(6):
            ok &= BITS[:,np.array(left)==port].sum(axis=1)<=1
            ok &= BITS[:,np.array(right)==port].sum(axis=1)<=1
        active = BITS[ok]
        spoke = np.zeros(len(active))
        for endpoints in [left,right]:
            for fac in [0,1]:
                blocked = sum(active[:,np.array(endpoints)==3*fac+port].sum(axis=1)*(1<<port)
                              for port in range(3))
                spoke += F[blocked]
        A = np.column_stack([spoke, active])
        obj = np.r_[4*sum(Q), np.full(4,.25), np.full(8,1/3)]
        ans = linprog(-obj,A_ub=A,b_ub=np.ones(len(A)),
                      bounds=[(0,None)]*13,method='highs')
        if not ans.success: raise RuntimeError(ans.message)
        if -ans.fun > best[0]+1e-9:
            best=(float(-ans.fun),(ap,bp))
            print('best',best,'scaled z,b',np.round(ans.x,6).tolist(),flush=True)
