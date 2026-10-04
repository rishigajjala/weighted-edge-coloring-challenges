"""Targeted stochastic-knapsack factor test for alpha=3/4.

One hub sees four single spokes of weights .51,.34,.26,.26.
Each leaf port has a mutually incompatible private blocker with mean x_i.
The hub's local law is the exact convex hull of feasible spoke subsets.
"""
import itertools
import json
import sys
import numpy as np
from scipy.optimize import differential_evolution, linprog

W=(.51,.34,.26,.26)
N=len(W)
ALPHA=.75
PATTERNS=[bits for bits in itertools.product((0,1),repeat=N)
          if sum(w*b for w,b in zip(W,bits))<=1+1e-10]
MAT=np.array(PATTERNS,dtype=float)


def local(x,q):
    vals=MAT@q
    res=linprog(-vals,A_ub=MAT.T,b_ub=1-x,
        A_eq=np.ones((1,len(PATTERNS))),b_eq=[1],
        bounds=[(0,None)]*len(PATTERNS),method='highs')
    if not res.success: raise RuntimeError(res.message)
    return -res.fun, res.x


def expected(x,q):
    avail=1-ALPHA*x
    out=0.
    for state in itertools.product((0,1),repeat=N):
        prob=np.prod(np.where(state,avail,1-avail))
        best=max(float(np.dot(pattern,q)) for pattern in PATTERNS
                 if all(not b or s for b,s in zip(pattern,state)))
        out+=prob*best
    return out


def ratio(a):
    x=np.array(a[:N]);q=np.array(a[N:])
    g,_=local(x,q);e=expected(x,q)
    return g/e if e>1e-10 else 0.


if __name__=='__main__':
    for seed in range(int(sys.argv[1]) if len(sys.argv)>1 else 3):
        res=differential_evolution(lambda a:-ratio(a),[(0,1)]*(2*N),
            seed=seed,maxiter=400,popsize=12,tol=1e-9,polish=True)
        x=np.array(res.x[:N]);q=np.array(res.x[N:])
        g,law=local(x,q);e=expected(x,q)
        print(json.dumps(dict(seed=seed,ratio=g/e,x=x.tolist(),q=q.tolist(),
            local=g,expected=e,
            law=[(list(PATTERNS[i]),float(v)) for i,v in enumerate(law)
                 if v>1e-7])),flush=True)
