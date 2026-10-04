"""Targeted bipartite 4-factor network with degree-two blocker ports.

Factor: one unit spoke worth 2 or two half spokes worth 1 each.
Each port has two unit blocker edges; blockers form two perfect
matchings between six left ports and six right ports. Probe balanced
vertex-local point: each factor uses the two spoke patterns half/half,
each incident blocker edge has marginal 1/4. No lower-bound claim.
"""
import numpy as np
from scipy.optimize import linprog

RNG = np.random.default_rng(20261003)
BITS = ((np.arange(1 << 12)[:, None] >> np.arange(12)) & 1).astype(np.uint8)
CS = np.linspace(0, 4, 2001)

def port_belongs(perm):
    # Left factor ports: 0..2 and 3..5. Right: 0..2 and 3..5.
    left = np.r_[np.arange(6), np.arange(6)]
    right = np.r_[np.arange(6), perm]
    return left, right

best = (0., None)
for trial in range(500):
    perm = RNG.permutation(6)
    left, right = port_belongs(perm)
    # A physical blocker set is a matching at each port.
    ok = np.ones(len(BITS), dtype=bool)
    for p in range(6):
        ok &= BITS[:, left == p].sum(axis=1) <= 1
        ok &= BITS[:, right == p].sum(axis=1) <= 1
    active = BITS[ok]
    spoke = np.zeros(len(active))
    for side in [left, right]:
        for lo in [0, 3]:
            masks = np.column_stack([active[:, side == p].sum(axis=1)
                                     for p in range(lo, lo + 3)])
            factor = np.maximum(2 * (masks[:, 0] == 0),
                                (masks[:, 1] == 0) + (masks[:, 2] == 0))
            spoke += factor
    k = active.sum(axis=1)
    bycount = np.array([spoke[k == j].max() for j in range(7)])
    M = (bycount[:, None] + np.arange(7)[:, None] * CS[None, :]).max(axis=0)
    L = 8 + 3 * CS  # 12 blocker edges * marginal 1/4
    ratios = L / M
    i = np.argmax(ratios)
    if ratios[i] > best[0] + 1e-9:
        best = (float(ratios[i]), trial)
        print('uniform best', best, 'perm', perm.tolist(),
              'c', float(CS[i]), 'bycount', bycount.tolist(), flush=True)
    # Optimize unequal blocker profits by Charnes-Cooper.
    A = np.column_stack([spoke, active])
    obj = np.r_[8., np.full(12, .25)]
    ans = linprog(-obj, A_ub=A, b_ub=np.ones(len(A)),
                  bounds=[(0, None)] * 13, method='highs')
    if not ans.success:
        raise RuntimeError(ans.message)
    if -ans.fun > best[0] + 1e-9:
        best = (float(-ans.fun), trial)
        print('weighted best', best, 'perm', perm.tolist(),
              'scaled z,b', np.round(ans.x, 6).tolist(), flush=True)
