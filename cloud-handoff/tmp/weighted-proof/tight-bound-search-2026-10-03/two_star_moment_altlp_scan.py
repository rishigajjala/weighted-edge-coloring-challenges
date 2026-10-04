import argparse

import numpy as np
from scipy.optimize import linprog

K = 4 / 3


def moments(d, y):
    p = (1 + 3 * d) / 4
    s = d - y
    mu = K * s / p
    t = min(s, 1 / 3)
    h = 3 * t * (1 - t) / (1 + 3 * t)
    var = (K / p) ** 2 * s * h
    return mu, var


def minimize_for_params(du, dv, y, grid, starts=3, steps=15, rng=None):
    pu = (1 + 3 * du) / 4
    pv = (1 + 3 * dv) / 4
    if pu * pv < 1 / 9:
        return None
    b = K * y / (pu * pv)
    mu_u, var_u = moments(du, y)
    mu_v, var_v = moments(dv, y)
    g = 1 / np.maximum.reduce([
        np.ones((len(grid), len(grid))),
        b + grid[:, None] + np.zeros((1, len(grid))),
        b + grid[None, :] + np.zeros((len(grid), 1)),
    ])
    constraints = []
    for mu, var in ((mu_u, var_u), (mu_v, var_v)):
        constraints.append((
            np.stack([grid ** 2]),
            np.array([mu * mu + var + 1e-12]),
            np.stack([np.ones(len(grid)), grid]),
            np.array([1, mu]),
        ))
    best = (2, None)
    for k in range(starts):
        if k == 0:
            j = np.searchsorted(grid, mu_v)
            j = min(max(1, j), len(grid) - 1)
            q = np.zeros(len(grid))
            q[j-1] = (grid[j] - mu_v) / (grid[j] - grid[j-1])
            q[j] = 1 - q[j-1]
        else:
            rnd = rng.random(len(grid))
            rnd /= rnd.sum()
            res = linprog(rnd, A_ub=constraints[1][0], b_ub=constraints[1][1], A_eq=constraints[1][2], b_eq=constraints[1][3], bounds=(0,None), method='highs')
            q = res.x if res.success else q
        p = None
        for _ in range(steps):
            res = linprog(g @ q, A_ub=constraints[0][0], b_ub=constraints[0][1], A_eq=constraints[0][2], b_eq=constraints[0][3], bounds=(0,None), method='highs')
            if not res.success: break
            p = res.x
            res = linprog(p @ g, A_ub=constraints[1][0], b_ub=constraints[1][1], A_eq=constraints[1][2], b_eq=constraints[1][3], bounds=(0,None), method='highs')
            if not res.success: break
            q = res.x
        if p is not None:
            val = K * p @ g @ q
            if val < best[0]:
                best = (val, (p.copy(), q.copy()))
    return best[0], b, mu_u, var_u, mu_v, var_v, best[1]


if __name__ == '__main__':
    parser = argparse.ArgumentParser()
    parser.add_argument('--trials', type=int, default=1000)
    parser.add_argument('--grid', type=int, default=101)
    parser.add_argument('--starts', type=int, default=2)
    parser.add_argument('--steps', type=int, default=10)
    args = parser.parse_args()
    grid = np.linspace(0, 16 / 3, args.grid)
    rng = np.random.default_rng(391991)
    worst = (2, None)
    for t in range(args.trials):
        du, dv = rng.random(2)
        y = min(du, dv) * rng.random() ** rng.uniform(.2, 4)
        out = minimize_for_params(du,dv,y,grid,args.starts,args.steps,rng)
        if out is None: continue
        if out[0] < worst[0]:
            worst = (out[0],(du,dv,y,out[1:6]))
            print('best',t,worst,flush=True)
            if worst[0]<.74999:break
