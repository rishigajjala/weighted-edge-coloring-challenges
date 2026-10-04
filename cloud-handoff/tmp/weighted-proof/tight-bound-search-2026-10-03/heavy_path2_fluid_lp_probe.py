"""Search support-function violations for one categorical heavy path of length two.

Exploratory only; no theorem is inferred from the output. Heavy edges are
(L0,R0),(L1,R0), so their scaled matching law is unique. Tiny edges are
arbitrary bipartite fluid edges on three left and three right vertices.
"""

from __future__ import annotations

import itertools
import random

import numpy as np
from scipy.optimize import linprog


ALPHA = 0.75
NL = NR = 3
V = NL + NR
ALL_EDGES = [(i, NL + j) for i in range(NL) for j in range(NR)]
HEAVY = [(0, NL), (1, NL)]


def recourse(edges, q, capacities):
    a = np.zeros((V, len(edges)))
    for k, (u, v) in enumerate(edges):
        a[u, k] = a[v, k] = 1
    sol = linprog(-np.asarray(q), A_ub=a, b_ub=capacities,
                  bounds=(0, None), method="highs")
    if not sol.success:
        raise RuntimeError(sol.message)
    return -sol.fun


def max_violation(edges, q, h1, h2):
    n = len(edges)
    a = np.zeros((V, n))
    for k, (u, v) in enumerate(edges):
        a[u, k] = a[v, k] = 1
    loads = np.zeros((V, 2))
    for j, ((u, v), h) in enumerate(zip(HEAVY, (h1, h2))):
        loads[u, j] = loads[v, j] = h
    full = recourse(edges, q, np.ones(V))
    residual_state = []
    for j in range(2):
        residual_state.append(recourse(edges, q, 1 - loads[:, j]))
    # Maximize alpha q.y - E F, with E F affine in x1,x2.
    coeff = np.r_[ALPHA * (full - np.array(residual_state)), ALPHA * np.array(q)]
    constraints = np.vstack((np.r_[np.ones(2), np.zeros(n)],
                             np.column_stack((loads, a))))
    rhs = np.r_[1, np.ones(V)]
    sol = linprog(-coeff, A_ub=constraints, b_ub=rhs,
                  bounds=(0, None), method="highs")
    if not sol.success:
        raise RuntimeError(sol.message)
    return -sol.fun - full, sol.x, (full, residual_state)


def main():
    rng = random.Random(20261003)
    best = (-1e9, None)
    for trial in range(6000):
        edges = [edge for edge in ALL_EDGES if rng.random() < 0.45]
        if not edges:
            continue
        q = [rng.choice((0.2, 0.5, 1.0, 2.0, 5.0)) for _ in edges]
        h1 = rng.choice((0.51, 0.6, 0.75, 0.9, 1.0))
        h2 = rng.choice((0.51, 0.6, 0.75, 0.9, 1.0))
        violation, point, rec = max_violation(edges, q, h1, h2)
        if violation > best[0]:
            best = (violation, (edges, q, h1, h2, point, rec))
            print("best", trial, violation, best[1], flush=True)
    print("final", best)


if __name__ == "__main__":
    main()
