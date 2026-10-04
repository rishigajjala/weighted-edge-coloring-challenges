import argparse
from itertools import product

import numpy as np
from scipy.optimize import differential_evolution


def ratio(x, m, n, K):
    # Variables: probe target, spoke target simplices, endpoint slack,
    # and neighboring vertex slack.  Endpoint target degrees stay <= 1.
    y = x[0]
    au = np.array(x[1 : 1 + m])
    av = np.array(x[1 + m : 1 + m + n])
    i = 1 + m + n
    capu, capv = x[i], x[i + 1]
    i += 2
    if y + au.sum() > 1 or y + av.sum() > 1:
        return 2 + max(y + au.sum() - 1, y + av.sum() - 1)
    du = y + au.sum() + (1 - y - au.sum()) * capu
    dv = y + av.sum() + (1 - y - av.sum()) * capv
    pu, pv = 0.25 + 0.75 * du, 0.25 + 0.75 * dv
    pu_spoke = 0.25 + 0.75 * (au + (1 - au) * np.array(x[i : i + m]))
    i += m
    pv_spoke = 0.25 + 0.75 * (av + (1 - av) * np.array(x[i : i + n]))
    b = min(K * y / (pu * pv), 12 * y)
    bu = np.minimum(K * au / (pu * pu_spoke), 12 * au)
    bv = np.minimum(K * av / (pv * pv_spoke), 12 * av)
    bu = np.nan_to_num(bu)
    bv = np.nan_to_num(bv)
    if m:
        bits_u = np.array(list(product((0.0, 1.0), repeat=m)))
        prob_u = np.prod(np.where(bits_u > 0, pu_spoke, 1 - pu_spoke), axis=1)
        load_u = bits_u @ bu
    else:
        prob_u = np.ones(1)
        load_u = np.zeros(1)
    if n:
        bits_v = np.array(list(product((0.0, 1.0), repeat=n)))
        prob_v = np.prod(np.where(bits_v > 0, pv_spoke, 1 - pv_spoke), axis=1)
        load_v = bits_v @ bv
    else:
        prob_v = np.ones(1)
        load_v = np.zeros(1)
    den = np.maximum.reduce(
        [
            np.ones((len(load_u), len(load_v))),
            b + load_u[:, None] + np.zeros((1, len(load_v))),
            b + load_v[None, :] + np.zeros((len(load_u), 1)),
        ]
    )
    expect = (prob_u[:, None] * prob_v[None, :] / den).sum()
    return (pu * pv * b / y) * expect


if __name__ == '__main__':
    parser = argparse.ArgumentParser()
    parser.add_argument('--spokes', type=int, default=4)
    parser.add_argument('--popsize', type=int, default=15)
    parser.add_argument('--maxiter', type=int, default=500)
    parser.add_argument('--K', type=float, default=4 / 3)
    args = parser.parse_args()
    m = n = args.spokes
    bounds = [(0.00001, 0.99999)] + [(0, 1)] * (m + n + 2 + m + n)
    opt = differential_evolution(
        lambda x: ratio(x, m, n, args.K),
        bounds,
        seed=9396,
        popsize=args.popsize,
        maxiter=args.maxiter,
        tol=1e-11,
        polish=True,
        workers=1,
    )
    print('ratio', opt.fun)
    print('x', opt.x)
    print('evaluations', opt.nfev)
