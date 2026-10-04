"""Small exact-state LP search for a 4/5 hull with per-edge cap K*y.

Each supervertex is a matched heavy pair with one left and one right
endpoint and shared binary free/occupied state. All tiny edges are
left_i--right_j, including optional internal i=j. No theorem claimed.
"""

import argparse
from itertools import product

import numpy as np
from scipy.optimize import linprog
from scipy.sparse import lil_matrix


def feasible(y, d, alpha=.8, kcap=4):
    m=len(d)
    edges=[(i,j) for i in range(m) for j in range(m) if y[i,j]>1e-10]
    states=np.array(list(product([0.,1.],repeat=m)))
    ns=len(states); ne=len(edges)
    nvar=ns*(1+ne)
    def zidx(s,e):return ns+s*ne+e
    eq=lil_matrix((m+1,nvar))
    eq[0,:ns]=1
    for i in range(m):eq[i+1,:ns]=states[:,i]
    beq=np.r_[1,(1-alpha)+alpha*d]
    ub=[]; rhs=[]
    for s in range(ns):
        for e,(i,j) in enumerate(edges):
            row={zidx(s,e):1,s:-kcap*y[i,j]}
            ub.append(row);rhs.append(0)
        for i in range(m):
            row={s:-states[s,i]}
            for e,(a,b) in enumerate(edges):
                if a==i:row[zidx(s,e)]=1
            ub.append(row);rhs.append(0)
            row={s:-states[s,i]}
            for e,(a,b) in enumerate(edges):
                if b==i:row[zidx(s,e)]=1
            ub.append(row);rhs.append(0)
    for e,(i,j) in enumerate(edges):
        row={zidx(s,e):-1 for s in range(ns)}
        ub.append(row);rhs.append(-alpha*y[i,j])
    A=lil_matrix((len(ub),nvar))
    for r,row in enumerate(ub):
        for c,v in row.items():A[r,c]=v
    out=linprog(np.zeros(nvar),A_ub=A.tocsr(),b_ub=rhs,
                A_eq=eq.tocsr(),b_eq=beq,bounds=(0,None),method='highs')
    return out.success,out.message


def max_uniform_factor(y,d,kcap=4):
    """Optimize common coordinate factor beta for the same joint-state LP."""
    m=len(d)
    edges=[(i,j) for i in range(m) for j in range(m) if y[i,j]>1e-10]
    states=np.array(list(product([0.,1.],repeat=m)))
    ns=len(states);ne=len(edges);nvar=ns*(1+ne)+1;bid=nvar-1
    def zidx(s,e):return ns+s*ne+e
    eq=lil_matrix((m+1,nvar));eq[0,:ns]=1
    for i in range(m):eq[i+1,:ns]=states[:,i]
    beq=np.r_[1,.2+.8*d]
    ub=[];rhs=[]
    for s in range(ns):
        for e,(i,j) in enumerate(edges):
            ub.append({zidx(s,e):1,s:-kcap*y[i,j]});rhs.append(0)
        for i in range(m):
            row={s:-states[s,i]}
            for e,(a,b) in enumerate(edges):
                if a==i:row[zidx(s,e)]=1
            ub.append(row);rhs.append(0)
            row={s:-states[s,i]}
            for e,(a,b) in enumerate(edges):
                if b==i:row[zidx(s,e)]=1
            ub.append(row);rhs.append(0)
    for e,(i,j) in enumerate(edges):
        row={zidx(s,e):-1 for s in range(ns)};row[bid]=y[i,j]
        ub.append(row);rhs.append(0)
    A=lil_matrix((len(ub),nvar))
    for r,row in enumerate(ub):
        for c,v in row.items():A[r,c]=v
    obj=np.zeros(nvar);obj[bid]=-1
    out=linprog(obj,A_ub=A.tocsr(),b_ub=rhs,A_eq=eq.tocsr(),
                b_eq=beq,bounds=(0,None),method='highs')
    return -out.fun if out.success else np.nan


if __name__=='__main__':
    pa=argparse.ArgumentParser();pa.add_argument('--pairs',type=int,default=4)
    pa.add_argument('--trials',type=int,default=1000)
    pa.add_argument('--kcap',type=float,default=4)
    args=pa.parse_args();rng=np.random.default_rng(9396);m=args.pairs
    for k in range(args.trials):
        y=rng.exponential(size=(m,m))
        y*=rng.choice([.1,.3,.6,1.],size=(m,m),p=[.3,.3,.25,.15])
        y*=rng.random((m,m))<rng.uniform(.3,1)
        # Matrix scaling to make all row/column sums <=1.
        for _ in range(8):
            rows=y.sum(axis=1);y*=np.minimum(1,1/np.maximum(rows,1e-12))[:,None]
            cols=y.sum(axis=0);y*=np.minimum(1,1/np.maximum(cols,1e-12))[None,:]
        min_d=np.maximum(y.sum(axis=1),y.sum(axis=0))
        d=min_d+(1-min_d)*rng.random(m)**rng.uniform(.5,4)
        ok,msg=feasible(y,d,kcap=args.kcap)
        if not ok:
            print('INFEASIBLE',k,'kcap',args.kcap,'y',y,'d',d,'message',msg,flush=True)
            break
        if k%100==0:print('checked',k,flush=True)
    else:print('all checked',args.trials)
