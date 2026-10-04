"""Exact small physical-color oracle for a factor-incoherent local point.

Each factor hub has 2 copies of weight .4, 3 of .3, and 3 of .26;
per-copy profits 1/2, 1/3, 1/3. The hub-local pattern takes one of
each bundle (profit 7/6). A port-local law alternates a full spoke
burst with one unit blocker, giving blocker marginals 1/2,2/3,2/3.

Four factors (two per bipartite shore). One blocker per port, so these
form a matching. A ports match A; B and C ports may mix. We enumerate
all topology types and optimize all nonnegative blocker profits for
this fixed valid vertex-local target by Charnes-Cooper LP.
"""
import itertools
import numpy as np
from scipy.optimize import linprog

W = np.array([.42, .31, .26])
Q = np.array([.55, .35, .30])
C = np.array([2, 3, 3])
F = np.zeros(8)
for blocked in range(8):
    for counts in itertools.product(*(range(c+1) for c in C)):
        if any(counts[i] and ((blocked >> i) & 1) for i in range(3)):
            continue
        if np.dot(W, counts) <= 1+1e-9:
            F[blocked] = max(F[blocked], np.dot(Q, counts))
print('factor f(blocked mask):', F.tolist(), flush=True)

BITS = ((np.arange(64)[:, None] >> np.arange(6)) & 1).astype(np.uint8)
best = (0., None)
for aperm in itertools.permutations((0, 1)):
    # Left factors 0,2 and right factors 1,3. Port indices 0=A,1=B,2=C.
    for bcperm in itertools.permutations((0, 1, 2, 3)):
        left = [0, 3, 1, 2, 4, 5]
        right = [3*aperm[0], 3*aperm[1]]
        right += [3*(bcperm[j]//2)+(bcperm[j]%2)+1 for j in range(4)]
        # right encoding factor 0/1 on right shore, port B/C; offsets
        # 0..2 represent global factor1, 3..5 represent global factor3.
        p = [.5, .5, 2/3, 2/3, 2/3, 2/3]
        spoke = np.zeros(len(BITS))
        for endpoints in [left, right]:
            for fac in [0, 1]:
                mask = np.zeros(len(BITS), dtype=np.uint8)
                for port in range(3):
                    mask += BITS[:, np.array(endpoints)==3*fac+port].sum(axis=1) * (1<<port)
                spoke += F[mask]
        A = np.column_stack([spoke, BITS])
        obj = np.r_[4*np.sum(Q), p]
        ans = linprog(-obj, A_ub=A, b_ub=np.ones(len(A)),
                      bounds=[(0, None)]*7, method='highs')
        if not ans.success:
            raise RuntimeError(ans.message)
        if -ans.fun > best[0] + 1e-9:
            best = (float(-ans.fun), (aperm, bcperm))
            print('best', best, 'scaled z,b', np.round(ans.x,6).tolist(), flush=True)
