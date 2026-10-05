"""Diagnostic for two-bin local phase obstruction; no bound claim."""
import argparse
import numpy as np
from scipy.linalg import null_space
from scipy.optimize import milp, LinearConstraint, Bounds


def sample(m, rng, delta):
    # m port nodes on each shore, grouped in pairs into m/2 physical vertices.
    triples = []
    for _ in range(3):
        perm = rng.permutation(m)
        triples += [(u, int(perm[u])) for u in range(m)]
    E = len(triples)
    A = np.zeros((2 * m, E))
    for j, (u, v) in enumerate(triples):
        A[u, j] = 1
        A[m + v, j] = 1
    ker = null_space(A)
    z = ker @ rng.normal(size=ker.shape[1])
    z *= delta / np.max(np.abs(z))
    w = np.ones(E) / 3 + z
    pair_l = rng.permutation(m)
    pair_r = rng.permutation(m)
    orig_l = np.empty(m, dtype=int)
    orig_r = np.empty(m, dtype=int)
    for i in range(m):
        orig_l[pair_l[i]] = i // 2
        orig_r[pair_r[i]] = i // 2
    V = m
    B = np.zeros((V, E))
    for j, (u, v) in enumerate(triples):
        B[orig_l[u], j] = w[j]
        B[m // 2 + orig_r[v], j] = w[j]
    assert np.max(np.abs(B.sum(axis=1) - 2)) < 1e-8
    sol = milp(-w, integrality=np.ones(E), bounds=Bounds(np.zeros(E), np.floor(1 / w)),
               constraints=LinearConstraint(B, -np.inf, np.ones(V)),
               options={"time_limit": 3.0, "mip_rel_gap": 1e-7})
    return -sol.fun if sol.status == 0 else None, m / 2, w, triples, orig_l, orig_r, sol


def main():
    p = argparse.ArgumentParser()
    p.add_argument("--ports", type=int, default=12)
    p.add_argument("--trials", type=int, default=30)
    p.add_argument("--delta", type=float, default=.09)
    args = p.parse_args()
    rng = np.random.default_rng(19771)
    best = (0, None)
    for i in range(args.trials):
        M, target, *rest = sample(args.ports, rng, args.delta)
        if M is None:
            continue
        ratio = target / M
        if ratio > best[0]:
            best = ratio, (i, M, target, rest)
    ratio, data = best
    print("best ratio", ratio, "trial", data[0], "global one-color weight", data[1], "local half-point weight", data[2])
    print("candidate above 4/3", ratio > 4 / 3)
    print("weight range", np.min(data[3][0]), np.max(data[3][0]))


if __name__ == "__main__":
    main()
