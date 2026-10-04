"""Targeted rank-two/rank-three factor shared-blocker diagnostic.

Four bipartite factors, seven guarded ports each. Every blocker pairs one
left and one right port. The tested local point mixes three full bins:
(.60,.40), (.55,.45), (.34,.33,.33), each with probability 1/3.
The program optimizes all nonnegative blocker profits for each matching.
This is only a finite-template diagnostic, not a theorem.
"""
import numpy as np
from scipy.optimize import linprog

W = np.array([.60, .40, .55, .45, .34, .33, .33])
NPORT = 7
F = np.zeros(1 << NPORT)
for block in range(1 << NPORT):
    free = [i for i in range(NPORT) if not (block >> i) & 1]
    for sel in range(1 << len(free)):
        weight = sum(W[free[i]] for i in range(len(free)) if (sel >> i) & 1)
        if weight <= 1 + 1e-9:
            F[block] = max(F[block], weight)

BITS = ((np.arange(1 << 14)[:, None] >> np.arange(14)) & 1).astype(np.uint8)
RNG = np.random.default_rng(20261003)
best = (0., None)
for trial in range(100):
    perm = RNG.permutation(14)
    masks = []
    for ports in [np.arange(7), perm[:7], np.arange(7, 14), perm[7:]]:
        masks.append((BITS[:, ports] * (1 << np.arange(7))).sum(axis=1))
    spoke = sum(F[mask] for mask in masks)
    A = np.column_stack([spoke, BITS])
    objective = np.r_[4., np.full(14, 2/3)]
    ans = linprog(-objective, A_ub=A, b_ub=np.ones(len(A)),
                  bounds=[(0, None)] * 15, method='highs')
    if not ans.success:
        raise RuntimeError(ans.message)
    ratio = -ans.fun
    if ratio > best[0] + 1e-7:
        best = (float(ratio), trial)
        print('best', best, 'perm', perm.tolist(),
              'scaled z,b', np.round(ans.x, 6).tolist(), flush=True)
