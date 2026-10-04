"""Two bipartite mixed-rank stars with degree-two shared blocker ports.

Prescribed local law: unit; half+half; third+third+third, each 1/3.
Each port has two unit blockers with marginal 1/3 apiece. Optimize
all nonnegative blocker profits for each small bipartite topology.
"""
import numpy as np
from scipy.optimize import linprog

W = np.array([1., .5, .5, 1/3, 1/3, 1/3])
F = np.zeros(64)
for block in range(64):
    free = [i for i in range(6) if not (block >> i) & 1]
    for sel in range(1 << len(free)):
        s = sum(W[free[i]] for i in range(len(free)) if (sel >> i) & 1)
        if s <= 1 + 1e-9:
            F[block] = max(F[block], s)

RNG = np.random.default_rng(20261003)
BITS = ((np.arange(1 << 12)[:, None] >> np.arange(12)) & 1).astype(np.uint8)
best = (0., None)
for trial in range(500):
    perm = RNG.permutation(6)
    left = np.r_[np.arange(6), np.arange(6)]
    right = np.r_[np.arange(6), perm]
    ok = np.ones(len(BITS), dtype=bool)
    for p in range(6):
        ok &= BITS[:, left == p].sum(axis=1) <= 1
        ok &= BITS[:, right == p].sum(axis=1) <= 1
    active = BITS[ok]
    ml = sum(active[:, left == p].sum(axis=1) * (1 << p) for p in range(6))
    mr = sum(active[:, right == p].sum(axis=1) * (1 << p) for p in range(6))
    spoke = F[ml] + F[mr]
    A = np.column_stack([spoke, active])
    obj = np.r_[2., np.full(12, 1/3)]
    ans = linprog(-obj, A_ub=A, b_ub=np.ones(len(A)),
                  bounds=[(0, None)] * 13, method='highs')
    if not ans.success:
        raise RuntimeError(ans.message)
    if -ans.fun > best[0] + 1e-9:
        best = (float(-ans.fun), trial)
        print('best', best, 'perm', perm.tolist(),
              'scaled z,b', np.round(ans.x, 6).tolist(), flush=True)
