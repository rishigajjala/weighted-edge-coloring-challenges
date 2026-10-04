"""Exact-state LP gauge on three heavy pairs and off-diagonal fluid C6.

This is a targeted diagnostic for extending the 5/4 paired-fluid path
mechanism.  The combined physical support is K3,3: heavy diagonal
edges L_i R_i, fluid off-diagonal edges L_i R_j (i != j).
All fluid is divisible and has no edge-supply bound.
"""

import itertools
import sys

import numpy as np
from scipy.optimize import linprog
from scipy.spatial import HalfspaceIntersection

K = 3
ARCS = [(i, j) for i in range(K) for j in range(K) if i != j]
STATES = list(itertools.product((0, 1), repeat=K))
S = len(STATES)
M = len(ARCS)
NVAR = S + S * M + 1
ALPHA = NVAR - 1


def local_lp(h, q):
    A = np.zeros((2 * K + K, K + M))
    b = np.ones(3 * K)
    for i in range(K):
        A[i, i] = h[i]
        A[K + i, i] = h[i]
        for e, (a, z) in enumerate(ARCS):
            if a == i:
                A[i, K + e] = 1
            if z == i:
                A[K + i, K + e] = 1
        A[2 * K + i, i] = 1
    r = linprog(-q, A_ub=A, b_ub=b, bounds=(0, None), method="highs")
    if not r.success:
        raise RuntimeError(r.message)
    return r.x


def global_alpha(h, target):
    Aeq = np.zeros((1 + K + M, NVAR))
    beq = np.zeros(1 + K + M)
    Aeq[0, :S] = 1
    beq[0] = 1
    for s, state in enumerate(STATES):
        for i in range(K):
            Aeq[1 + i, s] = state[i]
        for e in range(M):
            Aeq[1 + K + e, S + s * M + e] = 1
    Aeq[1 : 1 + K, ALPHA] = -target[:K]
    Aeq[1 + K :, ALPHA] = -target[K:]

    Aub = np.zeros((S * 2 * K, NVAR))
    bub = np.zeros(S * 2 * K)
    for s, state in enumerate(STATES):
        for i in range(K):
            for side in range(2):
                row = Aub[s * 2 * K + i * 2 + side]
                row[s] = -(1 - h[i] * state[i])
                for e, (a, z) in enumerate(ARCS):
                    if (side == 0 and a == i) or (side == 1 and z == i):
                        row[S + s * M + e] = 1
    c = np.zeros(NVAR)
    c[ALPHA] = -1
    bounds = [(0, None)] * (NVAR - 1) + [(0, 1)]
    r = linprog(c, A_ub=Aub, b_ub=bub, A_eq=Aeq, b_eq=beq,
                bounds=bounds, method="highs")
    if not r.success:
        raise RuntimeError(r.message)
    return -r.fun


def sweep(h, seed=0, draws=2000):
    rng = np.random.default_rng(seed)
    seen = set()
    best = (1.0, None, None)
    for t in range(draws):
        q = rng.exponential(size=K + M)
        if t % 3 == 0:
            q[rng.random(K + M) < 0.5] = 0
        elif t % 3 == 1:
            q = rng.integers(0, 4, size=K + M).astype(float)
        if not q.any():
            continue
        point = local_lp(h, q)
        key = tuple(np.round(point, 7))
        if key in seen:
            continue
        seen.add(key)
        alpha = global_alpha(h, point)
        if alpha < best[0] - 1e-8:
            best = alpha, point, q
            print("new best", t, "alpha", alpha, "gap", 1 / alpha,
                  "point", np.round(point, 6).tolist(),
                  "q", np.round(q, 6).tolist(), flush=True)
    print("FINAL weights", h.tolist(), "unique local vertices", len(seen),
          "best alpha", best[0], "gap", 1 / best[0])


def exhaustive(h, verbose=True):
    A = []
    b = []
    for i in range(K):
        for side in range(2):
            row = np.zeros(K + M)
            row[i] = h[i]
            for e, (a, z) in enumerate(ARCS):
                if (side == 0 and a == i) or (side == 1 and z == i):
                    row[K + e] = 1
            A.append(row)
            b.append(1)
    for i in range(K):
        row = np.zeros(K + M)
        row[i] = 1
        A.append(row)
        b.append(1)
    A.extend(-np.eye(K + M))
    b.extend(np.zeros(K + M))
    halfspaces = np.c_[np.array(A), -np.array(b)]
    vertices = HalfspaceIntersection(
        halfspaces, np.array([0.1] * K + [0.01] * M)
    ).intersections
    best = (1.0, None)
    for v in vertices:
        if max(v) < 1e-8:
            continue
        alpha = global_alpha(h, v)
        if alpha < best[0] - 1e-8:
            best = alpha, v
            if verbose:
                print("new best alpha", alpha, "gap", 1 / alpha,
                      "point", np.round(v, 8).tolist(), flush=True)
    if verbose:
        print("EXHAUSTIVE weights", h.tolist(), "local vertices", len(vertices),
              "best alpha", best[0], "gap", 1 / best[0])
    return best[0], best[1], len(vertices)


if __name__ == "__main__":
    h = np.array([float(x) for x in sys.argv[1].split(",")])
    if len(sys.argv) > 2 and sys.argv[2] == "exact":
        exhaustive(h)
    else:
        sweep(h, int(sys.argv[2]) if len(sys.argv) > 2 else 0,
              int(sys.argv[3]) if len(sys.argv) > 3 else 2000)
