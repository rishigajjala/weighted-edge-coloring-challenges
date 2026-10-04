"""Diagnostic for a stronger universal A/3 Jensen-gap matching-law lemma."""
import itertools
import json
import random
from pathlib import Path

import numpy as np
from scipy.optimize import linprog


def matchings(n, H):
    for bits in itertools.product((0, 1), repeat=len(H)):
        occ = np.zeros(n)
        for i, (u, v) in enumerate(H):
            if bits[i]:
                occ[u] += 1
                occ[v] += 1
        if max(occ) <= 1:
            yield np.array(bits, dtype=float)


def fluid_opt(n, F, q, cap):
    B = np.array([[int(v in edge) for edge in F] for v in range(n)])
    return -linprog(-np.array(q), A_ub=B, b_ub=cap,
                    bounds=(0, None), method="highs").fun


def case(n, H, F, w, x, q):
    alpha = 2 / 3
    Hinc = np.array([[int(v in edge) for edge in H] for v in range(n)])
    mm = np.array(list(matchings(n, H)))
    values = np.array([fluid_opt(n, F, q, 1 - Hinc @ (w * M)) for M in mm])
    Aeq = np.vstack([np.ones(len(mm)), mm.T])
    beq = np.r_[1, alpha * x]
    law = linprog(-values, A_eq=Aeq, b_eq=beq,
                  bounds=(0, None), method="highs")
    if not law.success:
        raise RuntimeError(law.message)
    G = -law.fun
    m = 1 - Hinc @ (w * x)
    ER = alpha * m + (1 - alpha) * np.ones(n)
    A = fluid_opt(n, F, q, np.ones(n))
    Fm = fluid_opt(n, F, q, m)
    FER = fluid_opt(n, F, q, ER)
    return dict(G=G, Fm=Fm, FER=FER, A=A,
                exact_margin=G - alpha * Fm,
                jensen_margin=A / 3 - (FER - G))


def run(trials=5000, seed=476813):
    rng = random.Random(seed)
    best = None
    for t in range(trials):
        n = rng.choice([4, 5, 6])
        pairs = list(itertools.combinations(range(n), 2))
        H = rng.sample(pairs, rng.randint(2, min(n + 2, len(pairs))))
        F = rng.sample(pairs, rng.randint(2, min(n + 3, len(pairs))))
        w = np.array([rng.choice([.50001, .6, .75, .9, 1.0]) for _ in H])
        # Generate a local point by an arbitrary nonnegative profit objective.
        p = np.array([rng.choice([0, 1, 2]) for _ in H])
        q = np.array([rng.choice([0, 1, 2]) for _ in F])
        A_loc = np.zeros((2 * n, len(H) + len(F)))
        for i, (u, v) in enumerate(H):
            A_loc[u, i] = A_loc[v, i] = 1
            A_loc[n + u, i] = A_loc[n + v, i] = w[i]
        for j, (u, v) in enumerate(F):
            A_loc[n + u, len(H) + j] = A_loc[n + v, len(H) + j] = 1
        loc = linprog(-np.r_[p, q], A_ub=A_loc, b_ub=np.ones(2 * n),
                      bounds=(0, None), method="highs")
        x = loc.x[:len(H)]
        result = case(n, H, F, w, x, q)
        if best is None or result["jensen_margin"] < best["result"]["jensen_margin"]:
            best = dict(trial=t, n=n, H=H, F=F, w=w.tolist(), x=x.tolist(),
                        q=q.tolist(), result=result)
            if result["jensen_margin"] < -1e-8:
                print("JENSEN FAIL", best, flush=True)
                break
        if result["exact_margin"] < -1e-8:
            print("EXACT FAIL", best, flush=True)
            break
    out = Path(__file__).with_suffix(".json")
    out.write_text(json.dumps(dict(trials=t + 1, best=best), indent=2))
    print("DONE", t + 1, "best jensen margin", best["result"]["jensen_margin"], flush=True)


if __name__ == "__main__":
    run()
