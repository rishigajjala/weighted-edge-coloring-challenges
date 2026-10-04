"""Random exact-LP feasibility search for the capped alpha=3/4 mixed hull.

Numerical exploration only. Each instance's feasibility LP includes a matching
probability and every state/edge fluid amount, so it tests one simultaneous
tiny target, rather than optimizing one profit direction at a time.
"""
import itertools
import json
import os
from pathlib import Path

import numpy as np
from scipy.optimize import linprog
from scipy.sparse import lil_matrix


RNG = np.random.default_rng(20261004)
ALPHA = float(os.environ.get("RESEARCH_ALPHA", "0.75"))
TRIALS = int(os.environ.get("RESEARCH_TRIALS", "2000"))
OUTPUT = Path(__file__).with_suffix(".json")


def matchings(edges):
    out = []
    for bits in itertools.product((0, 1), repeat=len(edges)):
        used = [v for j, e in enumerate(edges) if bits[j] for v in e]
        if len(used) == len(set(used)):
            out.append(np.array(bits, dtype=float))
    return np.array(out)


def make_case(k):
    n = 4 * k
    heavy_L = list(range(k))
    heavy_R = list(range(2 * k, 3 * k))
    private_L = list(range(k, 2 * k))
    private_R = list(range(3 * k, 4 * k))
    H = [(u, v) for u in heavy_L for v in heavy_R if RNG.random() < 0.75]
    if not H:
        H = [(heavy_L[0], heavy_R[0])]
    M = matchings(H)
    w = RNG.choice(np.array([0.5001, 0.51, 0.6, 0.75, 0.9, 1.0]), size=len(H))
    mixture = RNG.dirichlet(np.ones(len(M)) * RNG.choice([0.1, 0.4, 1.0]))
    x = mixture @ M
    D = np.ones(n)
    for j, (u, v) in enumerate(H):
        D[u] -= w[j] * x[j]
        D[v] -= w[j] * x[j]
    F = [(u, v) for u in heavy_L for v in heavy_R if RNG.random() < 0.8]
    F += [(u, private_R[u]) for u in heavy_L]
    F += [(private_L[v - 2 * k], v) for v in heavy_R]
    F = list(dict.fromkeys(F))
    inc = np.zeros((n, len(F)))
    for e, (u, v) in enumerate(F):
        inc[u, e] = inc[v, e] = 1
    ymax = RNG.choice(np.array([0.05, 0.08, 0.12, 0.25, 1.0]))
    ub = RNG.uniform(ymax * 0.4, ymax, len(F))
    q = RNG.lognormal(mean=0, sigma=1.2, size=len(F))
    sol = linprog(-q, A_ub=inc, b_ub=D, bounds=list(zip(np.zeros(len(F)), ub)), method="highs")
    assert sol.success, sol.message
    y = sol.x * RNG.choice(np.array([0.5, 0.8, 1.0]))
    C = 12 * y
    return H, F, M, w, x, y, C, D


def check_case(case):
    H, F, M, w, x, y, C, D = case
    nstates, nh = M.shape
    nf = len(F)
    n = len(D)
    # variable layout p_m followed by f_{m,e}.
    nv = nstates * (1 + nf)
    pi = lambda m: m * (1 + nf)
    fi = lambda m, e: m * (1 + nf) + 1 + e
    neq = 1 + nh + nf
    Aeq = lil_matrix((neq, nv))
    beq = np.r_[1.0, ALPHA * x, ALPHA * y]
    for m in range(nstates):
        Aeq[0, pi(m)] = 1
        for h in range(nh):
            Aeq[1 + h, pi(m)] = M[m, h]
        for e in range(nf):
            Aeq[1 + nh + e, fi(m, e)] = 1
    Aub = lil_matrix((nstates * (nf + n), nv))
    bub = np.zeros(nstates * (nf + n))
    for m in range(nstates):
        R = np.ones(n)
        for h, (u, v) in enumerate(H):
            R[u] -= w[h] * M[m, h]
            R[v] -= w[h] * M[m, h]
        for e in range(nf):
            row = m * (nf + n) + e
            Aub[row, fi(m, e)] = 1
            Aub[row, pi(m)] = -C[e]
        for v in range(n):
            row = m * (nf + n) + nf + v
            Aub[row, pi(m)] = -R[v]
            for e, (u, wv) in enumerate(F):
                if v == u or v == wv:
                    Aub[row, fi(m, e)] = 1
    sol = linprog(np.zeros(nv), A_eq=Aeq.tocsr(), b_eq=beq,
                  A_ub=Aub.tocsr(), b_ub=bub, bounds=(0, None),
                  method="highs")
    return sol


def as_json(case):
    H, F, M, w, x, y, C, D = case
    return {"H": H, "F": F, "w": w.tolist(), "x": x.tolist(),
            "y": y.tolist(), "C": C.tolist(), "D": D.tolist()}


best = None
for trial in range(TRIALS):
    k = int(RNG.choice([2, 2, 3]))
    case = make_case(k)
    sol = check_case(case)
    if sol.status == 2:
        rec = {"trial": trial, "case": as_json(case), "status": sol.message}
        OUTPUT.write_text(json.dumps(rec, indent=2))
        print("INFEASIBLE", json.dumps(rec), flush=True)
        break
    if not sol.success:
        print("UNKNOWN", trial, sol.status, sol.message, flush=True)
        continue
    if (trial + 1) % 100 == 0:
        print("PASS", trial + 1, flush=True)
else:
    print(f"Complete: no infeasible alpha={ALPHA} capped hull instance in {TRIALS} random cases.")
