"""Targeted four-factor bipartite three-phase shared-blocker diagnostic.

Not a lower-bound certificate: this probes one prescribed local law only.
"""
import itertools
import numpy as np
from scipy.optimize import linprog

W = np.array([1., .5, .5, 1/3, 1/3, 1/3])
F = np.zeros(64)
for block in range(64):
    available = [i for i in range(6) if not (block >> i) & 1]
    for sel in range(1 << len(available)):
        weight = sum(W[available[i]] for i in range(len(available)) if (sel >> i) & 1)
        if weight <= 1 + 1e-9:
            F[block] = max(F[block], weight)

STATES = np.arange(1 << 12, dtype=np.uint16)
BITS = ((STATES[:, None] >> np.arange(12)) & 1).astype(np.uint8)
NBIT = BITS.sum(axis=1)
CS = np.linspace(0, 1, 1001)
RNG = np.random.default_rng(20261003)

best = (0., None, None)
for trial in range(100):
    # Left factors 0,2 use columns 0..11; right factors 1,3 use a
    # random matching/permutation of those columns.
    perm = RNG.permutation(12)
    masks = []
    for ports in [np.arange(6), perm[:6], np.arange(6, 12), perm[6:]]:
        masks.append((BITS[:, ports] * (1 << np.arange(6))).sum(axis=1))
    spoke = sum(F[mask] for mask in masks)
    # Charnes-Cooper optimization of all nonnegative blocker profits b.
    # z=1/M and y=b/M. Every physical color bounds spoke*z + BITS@y <= 1.
    A = np.column_stack([spoke, BITS])
    objective = np.r_[4., np.full(12, 2/3)]
    ans = linprog(-objective, A_ub=A, b_ub=np.ones(len(A)),
                  bounds=[(0, None)] * 13, method='highs')
    if not ans.success:
        raise RuntimeError(ans.message)
    ratio = -ans.fun
    if ratio > best[0] + 1e-7:
        best = (float(ratio), trial, ans.x.tolist())
        print('best', ratio, 'perm', perm.tolist(), 'scaled z,b', np.round(ans.x, 6).tolist(), flush=True)
