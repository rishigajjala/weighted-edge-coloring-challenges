"""Exact finite-state LP probe for arbitrary unit-heavy supports and C=K*y.

Each matching is one heavy state. The LP jointly chooses its law and conditional
fluid flows, with one common retention factor alpha. Numerical output is evidence,
not a proof of a uniform theorem.
"""

import argparse
import json
from itertools import combinations

import numpy as np
from scipy.optimize import linprog
from scipy.sparse import coo_matrix


def matchings(n, edges):
    out = []
    def rec(i, used, chosen):
        if i == len(edges):
            out.append(tuple(chosen))
            return
        rec(i + 1, used, chosen)
        u, v = edges[i]
        if not (used & ((1 << u) | (1 << v))):
            chosen.append(i)
            rec(i + 1, used | (1 << u) | (1 << v), chosen)
            chosen.pop()
    rec(0, 0, [])
    return out


def retention_lp(n, h_edges, x, f_edges, y, kcap):
    keep_h = [i for i, a in enumerate(x) if a > 1e-11]
    h_edges = [h_edges[i] for i in keep_h]
    x = np.asarray(x)[keep_h]
    keep_f = [i for i, a in enumerate(y) if a > 1e-11]
    f_edges = [f_edges[i] for i in keep_f]
    y = np.asarray(y)[keep_f]
    ms = matchings(n, h_edges)
    ns, nf, nh = len(ms), len(f_edges), len(h_edges)
    zi = lambda s, e: ns + s * nf + e
    ai = ns * (nf + 1)
    nvar = ai + 1
    eqr, eqc, eqv, beq = [], [], [], np.zeros(1 + nh)
    beq[0] = 1
    for s, chosen in enumerate(ms):
        eqr.append(0); eqc.append(s); eqv.append(1)
        for e in chosen:
            eqr.append(1 + e); eqc.append(s); eqv.append(1)
    for e, a in enumerate(x):
        eqr.append(1 + e); eqc.append(ai); eqv.append(-float(a))
    aeq = coo_matrix((eqv, (eqr, eqc)), shape=(len(beq), nvar)).tocsr()

    ubr, ubc, ubv, bub = [], [], [], []
    def add_row(items, bound=0):
        row = len(bub)
        for col, val in items:
            ubr.append(row); ubc.append(col); ubv.append(val)
        bub.append(bound)
    incident = [[i for i, (u, v) in enumerate(f_edges) if u == a or v == a]
                for a in range(n)]
    for s, chosen in enumerate(ms):
        covered = {v for i in chosen for v in h_edges[i]}
        for v in range(n):
            if incident[v]:
                add_row([(zi(s, e), 1) for e in incident[v]] +
                        ([] if v in covered else [(s, -1)]))
        for e, target in enumerate(y):
            add_row([(zi(s, e), 1), (s, -kcap * float(target))])
    for e, target in enumerate(y):
        add_row([(zi(s, e), -1) for s in range(ns)] +
                [(ai, float(target))])
    aub = coo_matrix((ubv, (ubr, ubc)), shape=(len(bub), nvar)).tocsr()
    obj = np.zeros(nvar); obj[ai] = -1
    ans = linprog(obj, A_ub=aub, b_ub=bub, A_eq=aeq, b_eq=beq,
                  bounds=[(0, None)] * ai + [(0, 1)], method="highs")
    return (float(ans.x[ai]) if ans.success else None,
            {"success": bool(ans.success), "message": str(ans.message),
             "states": ns, "variables": nvar, "inequalities": len(bub)})


def fractional_point(n, h_edges, f_edges, rng, residual_palette):
    target_d = rng.choice(residual_palette, n)
    if h_edges:
        inc = np.zeros((n, len(h_edges)))
        for j, (u, v) in enumerate(h_edges): inc[u, j] = inc[v, j] = 1
        # Profit perturbations encourage both fractional odd-cycle and sparse faces.
        weights = rng.uniform(.1, 1, len(h_edges))
        if rng.random() < .35: weights[:] = 1 + rng.uniform(-.02, .02, len(h_edges))
        hsol = linprog(-weights, A_ub=inc, b_ub=1 - target_d,
                       bounds=(0, None), method="highs")
        if not hsol.success: raise RuntimeError(hsol.message)
        x = np.maximum(0, hsol.x)
        actual_d = 1 - inc @ x
    else:
        x = np.array([]); actual_d = np.ones(n)
    if f_edges:
        incf = np.zeros((n, len(f_edges)))
        for j, (u, v) in enumerate(f_edges): incf[u, j] = incf[v, j] = 1
        if rng.random() < .5:
            fweights = rng.uniform(.2, 1, len(f_edges))
            fsol = linprog(-fweights, A_ub=incf, b_ub=actual_d,
                           bounds=(0, None), method="highs")
            if not fsol.success: raise RuntimeError(fsol.message)
            y = np.maximum(0, fsol.x)
        else:
            y = rng.exponential(size=len(f_edges)) * rng.choice(
                [.001, .01, .1, 1], size=len(f_edges))
            for _ in range(20):
                loads = incf @ y
                ratio = np.minimum(1, actual_d / np.maximum(loads, 1e-15))
                y *= np.array([min(ratio[u], ratio[v]) for u, v in f_edges])
        # A nonextreme interior point can be harder than a single LP vertex.
        if rng.random() < .35: y *= rng.uniform(.05, 1)
    else: y = np.array([])
    return x, y, actual_d


def run(args):
    rng = np.random.default_rng(args.seed)
    n = args.n
    possible = ([(i, j) for i in range(n // 2) for j in range(n // 2, n)]
                if args.bip else list(combinations(range(n), 2)))
    pal = np.array([.001, .01, .05, .2, .4, .7, .95])
    best = {k: (2.0, None) for k in args.kcaps}
    for trial in range(args.trials):
        h_edges = [e for e in possible if rng.random() < rng.uniform(.25, .8)]
        f_edges = [e for e in possible if rng.random() < rng.uniform(.25, .8)]
        if not h_edges or not f_edges: continue
        x, y, d = fractional_point(n, h_edges, f_edges, rng, pal)
        if y.sum() < 1e-7: continue
        for k in args.kcaps:
            alpha, info = retention_lp(n, h_edges, x, f_edges, y, k)
            if alpha is None:
                print(json.dumps({"solver_failure": dict(trial=trial, K=k,
                     h_edges=h_edges, x=x.tolist(), f_edges=f_edges,
                     y=y.tolist(), info=info)}), flush=True)
                continue
            if alpha < best[k][0] - 1e-8:
                record = dict(trial=trial, n=n, bip=args.bip, K=k,
                              h_edges=h_edges, x=x.tolist(), f_edges=f_edges,
                              y=y.tolist(), D=d.tolist(), alpha=alpha,
                              lp=info)
                best[k] = (alpha, record)
                print(json.dumps({"best": record}), flush=True)
    print(json.dumps({"summary": {str(k): best[k][0] for k in args.kcaps},
                      "trials": args.trials, "seed": args.seed}), flush=True)


if __name__ == "__main__":
    p = argparse.ArgumentParser()
    p.add_argument("--n", type=int, default=6)
    p.add_argument("--bip", action="store_true")
    p.add_argument("--trials", type=int, default=100)
    p.add_argument("--seed", type=int, default=94622)
    p.add_argument("--kcaps", type=int, nargs="+", default=[2, 4, 12])
    run(p.parse_args())
