"""Cutting-plane polar gap for uniform demand on two pairable 2-factors.

Each type has N repeatable physical copies. The fixed local mean x=1/2
is witnessed by compatible H/M pairings at every vertex, so maximizing
its global polar value yields a valid asymptotic physical lower bound.
"""

import argparse
import json
import numpy as np
from scipy.optimize import Bounds, LinearConstraint, linprog, milp

BASE_H = [(i,4+(i+s)%4) for s in (0,1) for i in range(4)]
BASE_M = [(i,4+(i+s)%4) for s in (2,3) for i in range(4)]
BASE_W = [34,32,36,32,38,34,34,34,22,28,26,26,24,26,22,26]


def pairable(edges, weights, nv, nh):
    for v in range(nv):
        hs=sorted(weights[i] for i,e in enumerate(edges[:nh]) if v in e)
        ms=sorted(weights[nh+i] for i,e in enumerate(edges[nh:]) if v in e)
        if len(hs)!=2 or len(ms)!=2 or hs[0]+ms[1]>60 or hs[1]+ms[0]>60:
            return False
    return True


def lift(twists, perturb=None):
    base=BASE_H+BASE_M
    edges=[];weights=[]
    for i,((u,v),w,t) in enumerate(zip(base,BASE_W,twists)):
        for s in range(2):
            edges.append((2*u+s,2*v+(s^t)))
            weights.append(w+(0 if perturb is None else perturb[2*i+s]))
    return edges,weights,16,16


def polar_gap(edges,weights,nv,nh,max_iter=2000):
    d=len(edges)
    A=np.zeros((nv,d))
    for i,((u,v),w) in enumerate(zip(edges,weights)):
        A[u,i]=w; A[v,i]=w
    bounds=Bounds(np.zeros(d),np.r_[np.ones(nh),2*np.ones(d-nh)])
    capacity=LinearConstraint(A,-np.inf*np.ones(nv),60*np.ones(nv))
    cuts=np.eye(d).tolist()
    vals=[]
    for it in range(max_iter):
        lp=linprog(-.5*np.ones(d),A_ub=np.asarray(cuts),
                   b_ub=np.ones(len(cuts)),bounds=(0,None),method='highs')
        if not lp.success:raise RuntimeError(lp.message)
        p=lp.x
        sub=milp(-p,integrality=np.ones(d),bounds=bounds,
                 constraints=capacity,options={'time_limit':60})
        if sub.x is None:raise RuntimeError(('milp',sub.message))
        z=np.rint(sub.x).astype(int)
        value=float(p@z)
        if value<=1+1e-8:
            return dict(gap=-lp.fun,profits=p.tolist(),iterations=it,
                        active_profit_count=int(np.sum(p>1e-7)),
                        cuts=len(cuts))
        cuts.append(z.tolist())
        if it%100==0:print('PROGRESS',it,'upper',-lp.fun,'violation',value,flush=True)
    return dict(status='limit',gap_upper=-lp.fun,iterations=max_iter)


def main():
    ap=argparse.ArgumentParser()
    ap.add_argument('--lift',action='store_true')
    ap.add_argument('--perturb',action='store_true')
    ap.add_argument('--seed',type=int,default=0)
    args=ap.parse_args()
    if args.lift:
        rng=np.random.default_rng(args.seed)
        twists=rng.integers(0,2,size=16).tolist()
        edges,weights,nv,nh=lift(twists)
        if args.perturb:
            for trial in range(100000):
                delta=rng.integers(-2,3,size=32).tolist()
                edges,weights,nv,nh=lift(twists,delta)
                if pairable(edges,weights,nv,nh):
                    print('PERTURB',trial,delta,flush=True)
                    break
            else:
                raise RuntimeError('no locally pairable perturbation')
        print('TWISTS',twists,flush=True)
    else:
        edges=BASE_H+BASE_M;weights=BASE_W;nv=8;nh=8
    assert pairable(edges,weights,nv,nh)
    print('MODEL',json.dumps(dict(vertices=nv,types=len(edges),weights=weights)),flush=True)
    result=polar_gap(edges,weights,nv,nh)
    print('FINAL',json.dumps(result),flush=True)


if __name__=='__main__':main()
