"""Search for failure of a single heavy law to dominate product activation.

Numerical exploration only; profits are sampled, not exhaustively separated.
The benchmark is E independent Bernoulli(p) capped recourse, where
p_v=1-alpha*sum_{heavy e at v} w_e*x_e.
"""
import itertools
import json
import os
from pathlib import Path

import numpy as np
from scipy.optimize import linprog


RNG = np.random.default_rng(2026100402)
ALPHA = float(os.environ.get("RESEARCH_ALPHA", "0.75"))
TRIALS = int(os.environ.get("RESEARCH_TRIALS", "100"))
OUT = Path(__file__).with_suffix(".json")


def matchings(H):
    out = []
    for bits in itertools.product((0, 1), repeat=len(H)):
        used = [v for j, e in enumerate(H) if bits[j] for v in e]
        if len(used) == len(set(used)):
            out.append(np.array(bits, dtype=float))
    return np.array(out)


def recourse(q, inc, r, C):
    sol = linprog(-q, A_ub=inc, b_ub=r,
                  bounds=list(zip(np.zeros(len(C)), C)), method="highs")
    assert sol.success, sol.message
    return -sol.fun


def case(k):
    n = 4 * k
    HL = range(k)
    HR = range(2*k, 3*k)
    H = [(u, v) for u in HL for v in HR if RNG.random() < 0.8]
    if not H: H = [(0, 2*k)]
    M = matchings(H)
    w = RNG.choice([0.5001, 0.51, 0.6, 0.8, 1.0], size=len(H))
    mix = RNG.dirichlet(np.ones(len(M)) * RNG.choice([0.1, 0.5, 1.0]))
    x = mix @ M
    hinc = np.zeros((n, len(H)))
    for j, (u, v) in enumerate(H): hinc[u,j] = hinc[v,j] = 1
    D = 1 - hinc @ (w * x)
    F = [(u, v) for u in HL for v in HR if RNG.random() < 0.8]
    F += [(u, 3*k+u) for u in HL]
    F += [(k+v-2*k, v) for v in HR]
    F = list(dict.fromkeys(F))
    inc = np.zeros((n, len(F)))
    for j, (u, v) in enumerate(F): inc[u,j] = inc[v,j] = 1
    ub = RNG.uniform(0.03, RNG.choice([0.1, 0.3, 1.0]), size=len(F))
    ysol = linprog(-RNG.lognormal(0, 1.0, len(F)), A_ub=inc, b_ub=D,
                   bounds=list(zip(np.zeros(len(F)), ub)), method="highs")
    assert ysol.success
    y = ysol.x
    C = 12*y
    qs = []
    for j in range(len(F)):
        if y[j] > 1e-10:
            q = np.zeros(len(F)); q[j] = 1
            qs.append(q)
    for _ in range(12):
        q = RNG.lognormal(0, 1.5, len(F))
        q[y < 1e-10] = 0
        qs.append(q)
    return H, F, M, w, x, y, C, hinc, inc, qs


for trial in range(TRIALS):
    k = int(RNG.choice([2, 2, 3]))
    H, F, M, w, x, y, C, hinc, inc, qs = case(k)
    n, nh = hinc.shape
    active = np.where(hinc.sum(axis=1) > 0)[0]
    p = 1 - ALPHA * hinc @ (w*x)
    binary = []
    for bits in itertools.product((0,1), repeat=len(active)):
        r = np.ones(n)
        r[active] = bits
        prob = np.prod(np.where(np.array(bits), p[active], 1-p[active]))
        if prob > 1e-12: binary.append((r, prob))
    Rm = np.array([1 - hinc @ (w*m) for m in M])
    values = np.zeros((len(qs), len(M)))
    benchmark = np.zeros(len(qs))
    for j, q in enumerate(qs):
        values[j] = [recourse(q, inc, r, C) for r in Rm]
        benchmark[j] = sum(prob*recourse(q, inc, r, C) for r,prob in binary)
    Aeq = np.vstack((np.ones(len(M)), M.T))
    beq = np.r_[1.0, ALPHA*x]
    sol = linprog(np.zeros(len(M)), A_eq=Aeq, b_eq=beq,
                  A_ub=-values, b_ub=-benchmark,
                  bounds=(0,None), method="highs")
    if sol.status == 2:
        record = dict(trial=trial, H=H, F=F, w=w.tolist(), x=x.tolist(),
                      y=y.tolist(), p=p.tolist(), C=C.tolist(),
                      qs=[q.tolist() for q in qs], benchmark=benchmark.tolist(),
                      recourse=values.tolist())
        OUT.write_text(json.dumps(record, indent=2))
        print("UNIVERSAL LAW FAIL", json.dumps(record), flush=True)
        break
    if not sol.success:
        print("UNKNOWN", trial, sol.message, flush=True)
    if (trial+1)%10==0: print("PASS", trial+1, flush=True)
else:
    print(f"Complete: no universal-law failure in {TRIALS} sampled cases at alpha={ALPHA}.")
