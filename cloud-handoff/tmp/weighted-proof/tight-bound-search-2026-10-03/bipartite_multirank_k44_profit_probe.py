"""Targeted unequal-profit probe on K4,4 with two C8 weight factors.

The first factor uses shifts 0,1; the second shifts 2,3.  Each vertex
sees two types of each rank.  Exact local knapsack patterns are used;
the global one-color profit is solved as an integer program.  Search
outputs are numerical diagnostics and require rational verification.
"""

import itertools
import sys

import numpy as np
from scipy.optimize import Bounds, LinearConstraint, linprog, milp

EDGES = [(i, 4 + (i + shift) % 4) for shift in range(4) for i in range(4)]
D = len(EDGES)
NV = 8
W = np.zeros((NV, D))
for e, (u, v) in enumerate(EDGES):
    W[u, e] = W[v, e] = 1


def local_data(weights):
    pats = []
    inc = []
    for v in range(NV):
        ids = [e for e, uv in enumerate(EDGES) if v in uv]
        inc.append(ids)
        local = []
        for z in itertools.product(*(range(100 // weights[e] + 1)
                                     for e in ids)):
            if sum(weights[e] * c for e, c in zip(ids, z)) <= 100:
                local.append(z)
        pats.append(local)
    offsets = np.cumsum([0] + [len(p) for p in pats])
    Aeq = np.zeros((NV + D, offsets[-1]))
    b = np.r_[np.ones(NV), np.zeros(D)]
    P = np.zeros((D, offsets[-1]))
    for v in range(NV):
        Aeq[v, offsets[v]:offsets[v + 1]] = 1
        for j, p in enumerate(pats[v]):
            col = offsets[v] + j
            for e, c in zip(inc[v], p):
                if v < 4:
                    Aeq[NV + e, col] += c
                    P[e, col] += c
                else:
                    Aeq[NV + e, col] -= c
    return Aeq, b, P, [len(p) for p in pats]


def probe(weights, draws=1000, seed=0):
    Aeq, b, P, sizes = local_data(weights)
    Aub = W * np.array(weights)[None, :]
    upper = np.array([100 // w for w in weights], dtype=float)
    rng = np.random.default_rng(seed)
    best = (0, None, None, None, None)
    for t in range(draws):
        if t % 3 == 0:
            q = rng.integers(0, 4, size=D).astype(float)
        elif t % 3 == 1:
            q = rng.exponential(size=D)
            q[rng.random(D) < 0.4] = 0
        else:
            q = np.zeros(D)
            subset = rng.choice(D, size=rng.integers(3, 11), replace=False)
            q[subset] = rng.integers(1, 5, size=len(subset))
        if not q.any():
            continue
        lp = linprog(-(q @ P), A_eq=Aeq, b_eq=b, bounds=(0, None),
                     method="highs")
        if not lp.success:
            raise RuntimeError(lp.message)
        L = -lp.fun
        ip = milp(-q, integrality=np.ones(D),
                  bounds=Bounds(np.zeros(D), upper),
                  constraints=LinearConstraint(Aub, -np.inf, 100),
                  options={"mip_rel_gap": 1e-9})
        if not ip.success:
            raise RuntimeError(ip.message)
        M = -ip.fun
        gap = L / M
        if gap > best[0] + 1e-8:
            best = gap, q, P @ lp.x, ip.x, (L, M)
            print("BEST",t,"gap",gap,"L,M",L,M,
                  "q",np.round(q,5).tolist(),
                  "x",np.round(best[2],5).tolist(),flush=True)
    print("FINAL weights",weights,"local pattern counts",sizes,
          "gap",best[0],"draws",draws,flush=True)


if __name__ == "__main__":
    weights = [int(t) for t in sys.argv[1].split(",")]
    assert len(weights) == D
    probe(weights,int(sys.argv[2]) if len(sys.argv)>2 else 1000,
          int(sys.argv[3]) if len(sys.argv)>3 else 0)
