"""Numerical test of a separable sufficient bound for two-star recourse.

For independent one-side factors A,B in [0,c], min(A,B)>=AB/c.
If the product of their worst moment-relaxed means exceeds 9c/16,
the two-sided 3/4 inequality follows. This script only tests the claim.
"""

import argparse

import numpy as np
from scipy.optimize import differential_evolution, linprog

from two_star_moment_altlp_scan import K, moments


def one_side_min(d, y, b, grid):
    mu, var = moments(d, y)
    g = 1 / np.maximum(1, b + grid)
    out = linprog(g, A_ub=[grid**2], b_ub=[mu*mu+var+1e-11],
                  A_eq=[np.ones(len(grid)), grid], b_eq=[1, mu],
                  bounds=(0, None), method="highs")
    return out.fun if out.success else np.nan


def product_gap(params, grid):
    du, dv, f = params
    y = min(du, dv)*f
    pu, pv = (1+3*du)/4, (1+3*dv)/4
    if pu*pv < 1/9:
        return 1 + (1/9-pu*pv)
    b = K*y/(pu*pv)
    c = 1/max(1,b)
    au = one_side_min(du,y,b,grid)
    av = one_side_min(dv,y,b,grid)
    if np.isnan(au) or np.isnan(av):
        return 1
    return au*av/c - 9/16


if __name__ == "__main__":
    parser=argparse.ArgumentParser()
    parser.add_argument("--grid",type=int,default=81)
    parser.add_argument("--maxiter",type=int,default=250)
    args=parser.parse_args()
    grid=np.linspace(0,16/3,args.grid)
    opt=differential_evolution(lambda x: product_gap(x,grid),
                               [(0.01,1),(0.01,1),(0,1)],
                               seed=9396,popsize=10,maxiter=args.maxiter,
                               polish=True,tol=1e-9)
    print("min gap",opt.fun,"parameters",opt.x,"evaluations",opt.nfev)
    for du,dv,y in ((1,1,0),(1/3,1/3,1/3),(1,1/3,1/3),(.6,.6,.2)):
        print(du,dv,y,product_gap([du,dv,y/min(du,dv) if y else 0],grid))
