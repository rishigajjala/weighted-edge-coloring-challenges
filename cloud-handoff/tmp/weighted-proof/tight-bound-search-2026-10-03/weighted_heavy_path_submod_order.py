"""Finite LP check of a strong submodular-order coupling for heavy paths.

This tests a proof route, not the fractional edge-coloring theorem.  Given a
matching law M with specified edge marginals a, independently thin each edge
in M with its heavy weight w to obtain binary blockers B.  After flipping
right-shore availability bits, ask whether the resulting law dominates the
product law with the same vertex means against *all* submodular set functions.
"""

from itertools import combinations, product
import sys
import numpy as np
from scipy.optimize import linprog
from scipy.sparse import csc_matrix


def matching_masks(m):
    return [s for s in range(1 << m) if not (s & (s << 1))]


def state_mask(blockers, m):
    out = 0
    for v in range(m + 1):
        blocked = (v > 0 and bool(blockers & (1 << (v - 1)))) or (
            v < m and bool(blockers & (1 << v))
        )
        sigma = blocked if v % 2 else not blocked
        if sigma:
            out |= 1 << v
    return out


def distributions(a, w):
    m = len(a)
    n = m + 1
    matchings = matching_masks(m)
    laws = []
    for mask in matchings:
        edges = [e for e in range(m) if mask & (1 << e)]
        law = np.zeros(1 << n)
        for bits in product((0, 1), repeat=len(edges)):
            bmask = 0
            prob = 1.0
            for e, bit in zip(edges, bits):
                prob *= w[e] if bit else 1 - w[e]
                if bit:
                    bmask |= 1 << e
            law[state_mask(bmask, m)] += prob
        laws.append(law)
    p = np.ones(n)
    for e in range(m):
        p[e] -= a[e] * w[e]
        p[e + 1] -= a[e] * w[e]
    prod = np.zeros(1 << n)
    for mask in range(1 << n):
        prob = 1.0
        for v in range(n):
            sigma_p = p[v] if v % 2 == 0 else 1 - p[v]
            prob *= sigma_p if mask & (1 << v) else 1 - sigma_p
        prod[mask] = prob
    return matchings, np.array(laws).T, prod


def check(a, w):
    m = len(a)
    n = m + 1
    matchings, laws, prod = distributions(a, w)
    k = len(matchings)
    sq = []
    for i, j in combinations(range(n), 2):
        for base in range(1 << n):
            if base & ((1 << i) | (1 << j)):
                continue
            q = np.zeros(1 << n)
            q[base | (1 << i)] += 1
            q[base | (1 << j)] += 1
            q[base] -= 1
            q[base | (1 << i) | (1 << j)] -= 1
            sq.append(q)
    mat = np.column_stack([laws, -np.array(sq).T])
    marg = np.zeros((m + 1, mat.shape[1]))
    marg[0, :k] = 1
    for e in range(m):
        marg[e + 1, :k] = [bool(mask & (1 << e)) for mask in matchings]
    rhs = np.concatenate([prod, [1], a])
    Aeq = csc_matrix(np.vstack([mat, marg]))
    ans = linprog(np.zeros(mat.shape[1]), A_eq=Aeq, b_eq=rhs,
                  bounds=(0, None), method="highs")
    return ans, matchings


if __name__ == "__main__":
    m = int(sys.argv[1]) if len(sys.argv) > 1 else 4
    a = np.array([0.375] * m)
    w = np.array([0.51 if e % 2 == 0 else 1.0 for e in range(m)])
    ans, matchings = check(a, w)
    print("m", m, "a", a.tolist(), "w", w.tolist(), "feasible", ans.success)
    print(ans.message)
    if ans.success:
        print("matching probabilities", [(format(mask, f"0{m}b"), round(ans.x[i], 6))
              for i, mask in enumerate(matchings) if ans.x[i] > 1e-7])
