"""Targeted falsification of independent 2/3 blocker activation for one triangle factor.

Divisible spokes: direct edge has weight one and profit q; spoke profits
u,v per unit; each blocker has weight h>1/2. The original local hull
uses separate port patterns, with blocker means x,z.
"""
import json
import sys
from scipy.optimize import differential_evolution


def local(x, z, h, q, u, v):
    pmax = 1 - max(x, z)
    pivot = (1 - h * (x + z)) / 2
    candidates = [0.0, pmax]
    if 0 < pivot < pmax:
        candidates.append(pivot)
    best = -1
    best_state = None
    for p in candidates:
        L = 1 - h*x - p
        R = 1 - h*z - p
        if u >= v:
            l = L
            r = min(R, 1-l)
        else:
            r = R
            l = min(L, 1-r)
        value = q*p + u*l + v*r
        if value > best:
            best, best_state = value, (p,l,r)
    return best, best_state


def global_expectation(x, z, h, q, u, v):
    pi, pj = 2*x/3, 2*z/3
    f00 = max(q,u,v)
    f10 = v+(1-h)*max(u-v,0)
    f01 = u+(1-h)*max(v-u,0)
    f11 = (1-h)*(u+v)
    return ((1-pi)*(1-pj)*f00 + pi*(1-pj)*f10
            +(1-pi)*pj*f01+pi*pj*f11), (f00,f10,f01,f11)


def ratio(a):
    x,z,h,q,u,v = a
    lo,_ = local(x,z,h,q,u,v)
    hi,_ = global_expectation(x,z,h,q,u,v)
    return lo/hi if hi > 1e-12 else 0


if __name__ == '__main__':
    trials = int(sys.argv[1]) if len(sys.argv)>1 else 5
    for seed in range(trials):
        result = differential_evolution(lambda a:-ratio(a),
            [(0,1),(0,1),(.500001,1),(0,1),(0,1),(0,1)],
            seed=seed, maxiter=500, popsize=16, tol=1e-10, polish=True)
        a=result.x
        lo,state=local(*a)
        hi,vals=global_expectation(*a)
        print(json.dumps(dict(seed=seed, ratio=lo/hi, params=a.tolist(),
            local=lo, global_exp=hi, local_state=state, f_values=vals)),flush=True)
