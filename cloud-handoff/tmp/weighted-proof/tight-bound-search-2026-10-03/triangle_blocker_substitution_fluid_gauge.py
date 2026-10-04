"""Exact-state gauge for a five-vertex general-graph blocker substitution.

Vertices a,u,v,b,c.  Heavy pairs a-u (weight w) and v-b (weight 1).
Divisible fluid edges F=u-v, G1=a-c, G2=b-c.  Underlying support is
an odd five-cycle.  This combines a two-blocker positive-correlation
bottleneck with a competing two-spoke star at c.
"""

import sys

import numpy as np
from scipy.optimize import linprog
from scipy.spatial import HalfspaceIntersection

STATES = [(0, 0), (0, 1), (1, 0), (1, 1)]


def local_vertices(w):
    # Coordinates x1,x2,F,G1,G2.
    A = np.array([
        [1, 0, 0, 0, 0], [0, 1, 0, 0, 0],
        [w, 0, 1, 0, 0], [w, 0, 0, 1, 0],
        [0, 1, 1, 0, 0], [0, 1, 0, 0, 1],
        [0, 0, 0, 1, 1],
    ], dtype=float)
    b = np.ones(len(A))
    hs = np.vstack((np.c_[A, -b], np.c_[-np.eye(5), np.zeros(5)]))
    return HalfspaceIntersection(hs, np.array([.1] * 5)).intersections


def global_alpha(w, target):
    # Variables: lambda_s (4), F_s,G1_s,G2_s for each s (12), alpha.
    n = 17
    Aeq = np.zeros((6, n))
    beq = np.r_[1, np.zeros(5)]
    Aeq[0, :4] = 1
    for s, (z1, z2) in enumerate(STATES):
        Aeq[1, s] = z1
        Aeq[2, s] = z2
        for j in range(3):
            Aeq[3 + j, 4 + 3 * s + j] = 1
    Aeq[1:, -1] = -target

    Aub = np.zeros((5 * 4, n))
    for s, (z1, z2) in enumerate(STATES):
        r1, r2 = 1 - w * z1, 1 - z2
        F, G1, G2 = 4 + 3 * s, 5 + 3 * s, 6 + 3 * s
        rows = Aub[5 * s : 5 * s + 5]
        rows[0, s] = -r1; rows[0, F] = 1
        rows[1, s] = -r2; rows[1, F] = 1
        rows[2, s] = -r1; rows[2, G1] = 1
        rows[3, s] = -r2; rows[3, G2] = 1
        rows[4, s] = -1; rows[4, G1] = rows[4, G2] = 1
    c = np.zeros(n); c[-1] = -1
    lp = linprog(c, A_ub=Aub, b_ub=np.zeros(len(Aub)),
                 A_eq=Aeq, b_eq=beq,
                 bounds=[(0, None)] * 16 + [(0, 1)], method="highs")
    if not lp.success:
        raise RuntimeError(lp.message)
    return -lp.fun


def score(w):
    vertices = local_vertices(w)
    best = (1, None)
    for v in vertices:
        if max(v) < 1e-9:
            continue
        alpha = global_alpha(w, v)
        if alpha < best[0] - 1e-9:
            best = alpha, v
    print("w", w, "local vertices", len(vertices),
          "alpha", best[0], "gap", 1 / best[0],
          "point", None if best[1] is None else np.round(best[1], 8).tolist())


if __name__ == "__main__":
    for arg in sys.argv[1:]:
        score(float(arg))
