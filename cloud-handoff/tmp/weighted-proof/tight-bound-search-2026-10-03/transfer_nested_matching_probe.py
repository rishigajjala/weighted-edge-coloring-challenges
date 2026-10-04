"""Diagnostic of a nested actual-matching / binary-matching 2/3 lift."""
import itertools
import json
import random
from pathlib import Path

import numpy as np
from scipy.optimize import linprog
from scipy.sparse import coo_matrix


def nested_feasible(n, H, F, w, x, y, alpha=2 / 3):
    nh, nf = len(H), len(F)
    states = []
    for bits in itertools.product((0, 1), repeat=nh):
        M = [i for i, z in enumerate(bits) if z]
        used = [v for i in M for v in H[i]]
        if len(set(used)) != len(used):
            continue
        for sub in itertools.product((0, 1), repeat=len(M)):
            B = [i for i, z in zip(M, sub) if z]
            states.append((M, B))
    ns = len(states)
    nv = ns * (nf + 1)
    eqrows, eqcols, eqdata, eqrhs = [], [], [], []
    ubrows, ubcols, ubdata, ubrhs = [], [], [], []

    def add_eq(coeff, rhs):
        row = len(eqrhs)
        for col, val in coeff:
            eqrows.append(row);eqcols.append(col);eqdata.append(val)
        eqrhs.append(rhs)

    def add_ub(coeff, rhs):
        row = len(ubrhs)
        for col, val in coeff:
            ubrows.append(row);ubcols.append(col);ubdata.append(val)
        ubrhs.append(rhs)

    add_eq([(s * (nf + 1), 1) for s in range(ns)], 1)
    for e in range(nh):
        add_eq([(s * (nf + 1), 1) for s, (M, B) in enumerate(states) if e in M], alpha * x[e])
    for f in range(nf):
        add_eq([(s * (nf + 1) + 1 + f, 1) for s in range(ns)], alpha * y[f])
    # E[1_{e in B} | M] = w_e for every full matching M with positive mass.
    distinct_m = {tuple(M) for M, B in states}
    for M in distinct_m:
        for e in M:
            add_eq([(s * (nf + 1), (1 if e in B else 0) - w[e])
                    for s, (M2, B) in enumerate(states) if tuple(M2) == M], 0)
    for s, (M, B) in enumerate(states):
        blocked = {v for e in B for v in H[e]}
        for v in range(n):
            coeff = [(s * (nf + 1) + 1 + f, 1) for f, edge in enumerate(F) if v in edge]
            coeff.append((s * (nf + 1), -(0 if v in blocked else 1)))
            add_ub(coeff, 0)
    Aeq = coo_matrix((eqdata, (eqrows, eqcols)), shape=(len(eqrhs), nv)).tocsr()
    Aub = coo_matrix((ubdata, (ubrows, ubcols)), shape=(len(ubrhs), nv)).tocsr()
    sol = linprog(np.zeros(nv), A_eq=Aeq, b_eq=eqrhs,
                  A_ub=Aub, b_ub=ubrhs, bounds=(0, None), method="highs")
    return sol.success, ns, sol.message


def run(trials=3000, seed=623400):
    rng = random.Random(seed)
    best = None
    for t in range(trials):
        n = rng.choice([4, 5, 6])
        pairs = list(itertools.combinations(range(n), 2))
        H = rng.sample(pairs, rng.randint(2, min(n + 3, len(pairs))))
        F = rng.sample(pairs, rng.randint(2, min(n + 3, len(pairs))))
        w = np.array([rng.choice([.50001, .6, .75, .9, 1]) for _ in H])
        p = np.array([rng.choice([0, 1, 2, 3]) for _ in H])
        q = np.array([rng.choice([0, 1, 2, 3]) for _ in F])
        nh, nf = len(H), len(F)
        A = np.zeros((2 * n, nh + nf))
        for i, (u, v) in enumerate(H):
            A[u, i] = A[v, i] = 1
            A[n + u, i] = A[n + v, i] = w[i]
        for f, (u, v) in enumerate(F):
            A[n + u, nh + f] = A[n + v, nh + f] = 1
        loc = linprog(-np.r_[p, q], A_ub=A, b_ub=np.ones(2 * n),
                      bounds=(0, None), method="highs")
        x, y = loc.x[:nh], loc.x[nh:]
        ok, ns, msg = nested_feasible(n, H, F, w, x, y)
        if not ok:
            best = dict(trial=t, n=n, H=H, F=F, w=w.tolist(),
                        p=p.tolist(), q=q.tolist(), x=x.tolist(), y=y.tolist(),
                        states=ns, message=msg)
            print("NESTED FAIL", best, flush=True)
            break
        if t % 200 == 199:
            print(t + 1, "passed", flush=True)
    out = Path(__file__).with_suffix(".json")
    out.write_text(json.dumps(dict(seed=seed, trials=t + 1, candidate=best), indent=2))
    print("DONE", t + 1, "candidate", best is not None, flush=True)


if __name__ == "__main__":
    run()
