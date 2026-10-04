"""Exact-state LP probe of alpha=4/5, cap=4y with categorical heavy types."""

import argparse
from itertools import product
import numpy as np
from scipy.optimize import linprog
from scipy.sparse import lil_matrix


def feasible(y, residuals, probabilities, alpha=.8, kcap=4):
    m=len(residuals);states=np.array(list(product(range(3),repeat=m)))
    ns=len(states);edges=[(i,j) for i in range(m) for j in range(m) if y[i,j]>1e-10]
    ne=len(edges);nvar=ns*(1+ne)
    def zidx(s,e):return ns+s*ne+e
    eq=lil_matrix((1+2*m,nvar));eq[0,:ns]=1
    for i in range(m):
        eq[1+2*i,:ns]=(states[:,i]==0)
        eq[2+2*i,:ns]=(states[:,i]==1)
    beq=np.r_[1,np.array(probabilities)[:,:2].reshape(-1)]
    ub=[];rhs=[]
    for s in range(ns):
        for e,(i,j) in enumerate(edges):
            ub.append({zidx(s,e):1,s:-kcap*y[i,j]});rhs.append(0)
        for i in range(m):
            row={s:-residuals[i][states[s,i]]}
            for e,(a,b) in enumerate(edges):
                if a==i:row[zidx(s,e)]=1
            ub.append(row);rhs.append(0)
            row={s:-residuals[i][states[s,i]]}
            for e,(a,b) in enumerate(edges):
                if b==i:row[zidx(s,e)]=1
            ub.append(row);rhs.append(0)
    for e,(i,j) in enumerate(edges):
        ub.append({zidx(s,e):-1 for s in range(ns)})
        rhs.append(-alpha*y[i,j])
    A=lil_matrix((len(ub),nvar))
    for r,row in enumerate(ub):
        for c,v in row.items():A[r,c]=v
    out=linprog(np.zeros(nvar),A_ub=A.tocsr(),b_ub=rhs,A_eq=eq.tocsr(),
                b_eq=beq,bounds=(0,None),method='highs')
    return out.success,out.message


if __name__=='__main__':
    pa=argparse.ArgumentParser();pa.add_argument('--pairs',type=int,default=3)
    pa.add_argument('--trials',type=int,default=1000)
    args=pa.parse_args();m=args.pairs;rng=np.random.default_rng(9396)
    for k in range(args.trials):
        residuals=np.column_stack([np.ones(m),rng.uniform(0,.49,m),rng.uniform(0,.49,m)])
        heavy_total=rng.uniform(0,.8,m)
        split=rng.random(m)
        probs=np.column_stack([1-heavy_total,heavy_total*split,heavy_total*(1-split)])
        p=(residuals*probs).sum(axis=1)
        d=(p-.2)/.8
        y=rng.exponential(size=(m,m));y*=rng.random((m,m))<rng.uniform(.3,1)
        y*=rng.choice([.01,.1,.5,1],size=(m,m))
        for _ in range(10):
            rows=y.sum(axis=1);y*=np.minimum(1,d/np.maximum(rows,1e-12))[:,None]
            cols=y.sum(axis=0);y*=np.minimum(1,d/np.maximum(cols,1e-12))[None,:]
        ok,msg=feasible(y,residuals,probs)
        if not ok:
            print('INFEASIBLE',k,'y',y,'residuals',residuals,'probs',probs,'D',d,'msg',msg,flush=True)
            break
        if k%100==0:print('checked',k,flush=True)
    else:print('all checked',args.trials)
