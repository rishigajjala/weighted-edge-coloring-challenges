"""Diagnostic search, not a proof: exact local LP versus global mixed MILP."""
import itertools
import json
import random
from pathlib import Path

import numpy as np
from scipy.optimize import Bounds, LinearConstraint, linprog, milp


def compare(n, heavy, fluid, weight, profit_h, profit_f):
    m, k = len(heavy), len(fluid)
    A = np.zeros((2 * n, m + k))
    for i, (u, v) in enumerate(heavy):
        A[u, i] = A[v, i] = 1
        A[n + u, i] = A[n + v, i] = weight[i]
    for j, (u, v) in enumerate(fluid):
        A[n + u, m + j] = A[n + v, m + j] = 1
    p = np.r_[profit_h, profit_f]
    local = linprog(-p, A_ub=A, b_ub=np.ones(2 * n), bounds=(0, None), method="highs")
    if not local.success:
        raise RuntimeError(local.message)
    # The global one-pattern MILP uses the same weighted degree constraints
    # and enforces at most one heavy edge per vertex through binary variables.
    global_sol = milp(
        -p,
        integrality=np.r_[np.ones(m), np.zeros(k)],
        bounds=Bounds(np.zeros(m + k), np.r_[np.ones(m), np.ones(k)]),
        constraints=LinearConstraint(A, -np.inf, np.ones(2 * n)),
        options={"mip_rel_gap": 1e-10},
    )
    if not global_sol.success:
        raise RuntimeError(global_sol.message)
    return -local.fun, -global_sol.fun, local.x, global_sol.x


def run(seed=20261003, trials=10000):
    rng = random.Random(seed)
    best = None
    for t in range(trials):
        n = rng.choice([5, 6, 7, 8])
        pairs = list(itertools.combinations(range(n), 2))
        heavy = rng.sample(pairs, rng.randint(n - 1, min(len(pairs), n + 5)))
        fluid = rng.sample(pairs, rng.randint(n - 1, min(len(pairs), n + 6)))
        weight = [rng.choice([.50001, .55, .6, 2 / 3, .75, .85, .95, 1.0]) for _ in heavy]
        if t % 2:
            # Local-dual-generated objective concentrates on potentially tight rows.
            a = np.array([rng.choice([0, 0, 0, rng.random(), rng.random()]) for _ in range(n)])
            b = np.array([rng.choice([0, 0, 0, rng.random(), rng.random()]) for _ in range(n)])
            profit_h = np.array([a[u] + a[v] + w * (b[u] + b[v]) for (u, v), w in zip(heavy, weight)])
            profit_f = np.array([b[u] + b[v] for u, v in fluid])
            profit_h *= np.array([rng.choice([0, 1, 1, 1]) for _ in heavy])
            profit_f *= np.array([rng.choice([0, 1, 1, 1]) for _ in fluid])
        else:
            profit_h = np.array([rng.choice([0, 1, 1, 1]) * rng.uniform(.2, 2) for _ in heavy])
            profit_f = np.array([rng.choice([0, 1, 1, 1]) * rng.uniform(.2, 2) for _ in fluid])
        L, C, x, g = compare(n, heavy, fluid, weight, profit_h, profit_f)
        if C < 1e-10:
            continue
        ratio = L / C
        if best is None or ratio > best["ratio"]:
            best = dict(
                trial=t, ratio=ratio, n=n, heavy=heavy, fluid=fluid,
                weight=weight, profit_h=profit_h.tolist(), profit_f=profit_f.tolist(),
                local=L, global_value=C, local_point=x.tolist(), global_pattern=g.tolist(),
            )
            if ratio > 1.5000001:
                break
        if t % 1000 == 999:
            print(t + 1, "best", best["ratio"], flush=True)
    out = Path(__file__).with_suffix(".json")
    out.write_text(json.dumps(dict(seed=seed, trials=t + 1, best=best), indent=2))
    print("DONE", t + 1, "best", best["ratio"], "output", out, flush=True)


if __name__ == "__main__":
    run()
