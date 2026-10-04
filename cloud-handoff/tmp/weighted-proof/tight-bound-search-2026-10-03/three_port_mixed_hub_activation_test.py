"""Targeted alpha=3/4 factor test for a 3-port mixed-rank knapsack hub.

Spoke bundles: weights (.4,.3,.26), port capacities (2,3,3),
selected .7 blocker leaves residual spoke capacities (0,1,1).
Each blocker is a distinct matching edge incident to its port.
"""
import itertools
import json
import sys
import numpy as np
from scipy.optimize import differential_evolution,linprog

W=np.array([.4,.3,.26])
K=np.array([2,3,3])
R=np.array([0,1,1])
ALPHA=.75
PAT=np.array([counts for counts in itertools.product(*(range(k+1) for k in K))
              if np.dot(W,counts)<=1+1e-10],dtype=float)


def local(x,q):
    caps=K-(K-R)*x
    val=PAT@q
    res=linprog(-val,A_ub=PAT.T,b_ub=caps,
        A_eq=np.ones((1,len(PAT))),b_eq=[1],
        bounds=[(0,None)]*len(PAT),method='highs')
    if not res.success: raise RuntimeError(res.message)
    return -res.fun,res.x


def expected(x,q):
    p=ALPHA*x
    out=0
    table=[]
    for state in itertools.product((0,1),repeat=3):
        prob=np.prod(np.where(state,p,1-p))
        caps=np.where(state,R,K)
        good=PAT[np.all(PAT<=caps,axis=1)]
        best=max(good@q)
        out+=prob*best
        table.append((state,best))
    return out,table


def ratio(a):
    x=a[:3];q=a[3:]
    g,_=local(x,q)
    e,_=expected(x,q)
    return g/e if e>1e-9 else 0


if __name__=='__main__':
    for seed in range(int(sys.argv[1]) if len(sys.argv)>1 else 3):
        res=differential_evolution(lambda a:-ratio(a),[(0,1)]*6,
            seed=seed,maxiter=400,popsize=12,tol=1e-9,polish=True)
        x=res.x[:3];q=res.x[3:]
        g,law=local(x,q);e,table=expected(x,q)
        print(json.dumps(dict(seed=seed,ratio=g/e,x=x.tolist(),q=q.tolist(),
            local=g,expected=e,law=[(PAT[i].tolist(),float(v))
            for i,v in enumerate(law) if v>1e-7],table=table)),flush=True)
