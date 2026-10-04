"""Diagnostic only: one alternating heavy path and a fluid matching.

The LP computes a true (uncapped fluid) one-color hull gauge by enumerating
every heavy matching. It is not a proof for arbitrary weights or supports.
"""
import itertools
import json
import numpy as np
from scipy.optimize import linprog


def matchings(m):
    return np.array([b for b in itertools.product([0, 1], repeat=m)
                     if all(not (b[i] and b[i+1]) for i in range(m-1))], float)


def gauge(w, pairs, p, states):
    m = len(w)
    occ = states * w
    loads = np.zeros((len(states), m+1))
    loads[:, :-1] += occ
    loads[:, 1:] += occ
    residual = 1-loads
    caps = np.array([np.minimum(residual[:, u], residual[:, v])
                     for u, v in pairs])
    x = np.array([p if i % 2 == 0 else 1-p for i in range(m)])
    local = np.zeros(m+1)
    local[:-1] += x*w
    local[1:] += x*w
    y = np.array([1-max(local[u], local[v]) for u, v in pairs])
    aeq = np.vstack([np.r_[np.ones(len(states)), 0],
                     np.column_stack([states.T, -x])])
    beq = np.r_[1, np.zeros(m)]
    aub = np.column_stack([-caps, y])
    res = linprog(np.r_[np.zeros(len(states)), -1], A_eq=aeq, b_eq=beq,
                  A_ub=aub, b_ub=np.zeros(len(pairs)),
                  bounds=[(0, None)]*len(states)+[(0, 1)], method='highs')
    assert res.success, res.message
    return res.x[-1], y, res


def main():
    cases = [(8, [(0,7),(2,5),(1,4),(3,6)]),
             (7, [(0,5),(2,7),(1,4),(3,6)])]
    best = {'alpha': 1.0}
    count = 0
    for m, pairs in cases:
        st = matchings(m)
        for wt in itertools.product([.5, 1.], repeat=m):
            w = np.array(wt)
            for p in [1/4, 1/3, .4, .5, .6, 2/3, 3/4]:
                alpha, y, res = gauge(w, pairs, p, st)
                count += 1
                if alpha < best['alpha']-1e-9:
                    best = {'alpha': float(alpha), 'm': m,
                            'pairs': pairs, 'weights': wt, 'p': p,
                            'y': y.tolist()}
                    print(json.dumps({'count': count, 'best': best}), flush=True)
        print(json.dumps({'completed_m': m, 'count': count, 'best': best}), flush=True)
    print(json.dumps({'finished': True, 'count': count, 'best': best}), flush=True)


if __name__ == '__main__':
    main()
