"""Exact local-vertex/polar optimization for the targeted two-rank model."""

import itertools
import json
import importlib
import sys
import numpy as np
from scipy.optimize import linprog
model = importlib.import_module(sys.argv[1] if len(sys.argv) > 1
                                else "bipartite_mixed_rank_two_three_guard")


def local_vertices():
    out = {}
    n = len(model.STATES)
    for k in (1, 2, 3):
        for support in itertools.combinations(range(n), k):
            a = model.LOCAL_EQ[:, support]
            if np.linalg.matrix_rank(a, tol=1e-9) < k:
                continue
            lam = np.linalg.lstsq(a, model.LOCAL_RHS, rcond=None)[0]
            if np.max(np.abs(a @ lam - model.LOCAL_RHS)) > 1e-9 or min(lam) < -1e-9:
                continue
            x = lam @ model.P[list(support), :]
            key = tuple(np.round(x, 10))
            out.setdefault(key, (x, support, lam))
    return list(out.values())


def gauge(x, reverse_b=False):
    nn = len(model.NODES)
    ns = len(model.STATES)
    dim = model.P.shape[1]
    a = np.zeros((ns, dim + nn - 1))
    a[:, :dim] = model.P
    for j, s in enumerate(model.STATES):
        if reverse_b:
            src = model.NODE_INDEX[(s[0], s[3])]
            dst = model.NODE_INDEX[(s[2], s[1])]
        else:
            src = model.NODE_INDEX[(s[0], s[1])]
            dst = model.NODE_INDEX[(s[2], s[3])]
        if src:
            a[j, dim + src - 1] -= 1
        if dst:
            a[j, dim + dst - 1] += 1
    c = np.zeros(a.shape[1]); c[:dim] = -x
    result = linprog(c, A_ub=a, b_ub=np.ones(ns),
                     bounds=[(0, None)] * dim + [(None, None)] * (nn - 1),
                     method="highs")
    if not result.success:
        raise RuntimeError(result.message)
    return -result.fun, result.x[:dim]


def main():
    vertices = local_vertices()
    for reverse_b in (False, True):
        best = (0, None)
        for x, support, lam in vertices:
            ratio, p = gauge(x, reverse_b=reverse_b)
            if ratio > best[0] + 1e-8:
                best = (ratio, {"ratio": ratio, "profit": p.tolist(),
                                "local_mean": x.tolist(),
                                "support": [(model.STATES[j], float(t))
                                            for j, t in zip(support, lam)]})
                print("BEST", reverse_b, json.dumps(best[1]), flush=True)
        print("FINAL", json.dumps({"reverse_b": reverse_b,
                                    "local_vertices": len(vertices),
                                    "best": best[1]}), flush=True)


if __name__ == "__main__":
    main()
