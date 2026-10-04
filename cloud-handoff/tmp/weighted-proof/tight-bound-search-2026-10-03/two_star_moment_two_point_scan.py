import numpy as np
from scipy.optimize import differential_evolution


K = 4 / 3


def objective(x):
    du, dv, yf, theta_u, theta_v = x
    y = yf * min(du, dv)
    pu, pv = (1 + 3 * du) / 4, (1 + 3 * dv) / 4
    pp = pu * pv
    if pp < 1 / 9:
        return 2 + 1 / 9 - pp
    b = K * y / pp
    means = [K * (du - y) / pu, K * (dv - y) / pv]
    vars_ = []
    for d, p in ((du, pu), (dv, pv)):
        s = d - y
        t = min(s, 1 / 3)
        h = 3 * t * (1 - t) / (1 + 3 * t)
        vars_.append((K / p) ** 2 * s * h)
    vals = []
    probs = []
    for mu, var, theta in zip(means, vars_, (theta_u, theta_v)):
        if mu < 1e-12:
            vals.append([0, 0])
            probs.append([1, 0])
        else:
            top = mu + theta * var / mu
            prob = mu / top
            vals.append([0, top])
            probs.append([1 - prob, prob])
    eg = sum(
        probs[0][i] * probs[1][j] / max(1, b + vals[0][i], b + vals[1][j])
        for i in range(2)
        for j in range(2)
    )
    return K * eg


if __name__ == '__main__':
    bounds = [(0, 1), (0, 1), (0, 1), (0, 1), (0, 1)]
    for seed in (11, 711, 1819, 2221):
        opt = differential_evolution(
            objective,
            bounds,
            seed=seed,
            popsize=40,
            maxiter=2000,
            tol=1e-12,
            polish=True,
        )
        print(seed, opt.fun, opt.x, flush=True)
