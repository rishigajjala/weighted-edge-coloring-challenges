"""Minimax vertex deficit for random mean-feasible extreme flows.
Numerical exploration only, retaining exact per-pair two-point marginals.
"""
import itertools,json,time
from pathlib import Path
import numpy as np
from scipy.optimize import linprog
from scipy.sparse import lil_matrix
rng=np.random.default_rng(31026111)
OUT=Path(__file__).with_suffix('.json')

def check(n,k,edges,low,high,prob,q):
    inc=np.array([[float(v in e) for e in edges] for v in range(n)])
    mean=np.ones(n); mean[:2*k]=np.repeat(low+(high-low)*prob,2)
    r=linprog(-q,A_ub=inc,b_ub=mean,bounds=(0,None),method='highs')
    assert r.success
    keep=np.flatnonzero(r.x>1e-9); y=r.x[keep];inc=inc[:,keep]
    edges=[edges[j] for j in keep];m=len(edges)
    states=np.array(list(itertools.product([0,1],repeat=k)));s=len(states)
    nv=s*(m+1)+1
    eq=np.zeros((k+1,nv));eq[0,:s]=1;eq[1:,:s]=states.T
    ub=lil_matrix((s*n+m+n,nv));rhs=np.r_[np.zeros(s*n),y,-inc@y]
    for j,state in enumerate(states):
        cap=np.ones(n);cap[:2*k]=np.repeat(low+(high-low)*state,2)
        ub[j*n:(j+1)*n,j]=-cap[:,None]
        ub[j*n:(j+1)*n,s+j*m:s+(j+1)*m]=inc
        ub[s*n:s*n+m,s+j*m:s+(j+1)*m]=np.eye(m)
        ub[s*n+m:,s+j*m:s+(j+1)*m]=-inc
    ub[s*n+m:,-1]=-1
    obj=np.zeros(nv);obj[-1]=1
    r=linprog(obj,A_ub=ub.tocsr(),b_ub=rhs,A_eq=eq,b_eq=np.r_[1,prob],
              bounds=(0,None),method='highs')
    assert r.success,r.message
    return r.fun,dict(n=n,k=k,edges=edges,y=y.tolist(),low=low.tolist(),high=high.tolist(),
        prob=prob.tolist(),means=mean.tolist(),coupling=r.x[:s].tolist())

def main():
    start=time.monotonic();best={'deficit':-1};count=0
    for trial in range(16000):
        k=int(rng.choice([3,4,5]));n=2*k+int(rng.choice([0,1,2,3]))
        edges=[(u,v) for u in range(n) for v in range(u+1,n) if rng.random()<.4]
        if not edges:continue
        low=rng.choice([0,0,0,.1,.2,.3,.5],k).astype(float)
        high=low+(1-low)*rng.choice([.5,.75,1,1,1],k)
        prob=rng.choice([.1,.2,.3,.4,.5,.6,.7,.8,.9],k)
        q=rng.choice([.5,1,1,1,1.5,2],len(edges))
        d,rec=check(n,k,edges,low,high,prob,q);count+=1
        if d>best['deficit']+1e-9:
            best={'deficit':float(d),**rec}
            print('BEST',count,d,flush=True)
            OUT.write_text(json.dumps(dict(count=count,best=best,finished=False),indent=2))
        if d>.5000001:break
        if trial%1000==0:print('PROGRESS',trial,round(time.monotonic()-start,1),flush=True)
    OUT.write_text(json.dumps(dict(count=count,best=best,finished=True,seconds=time.monotonic()-start),indent=2))
    print('DONE',count,best['deficit'],flush=True)
if __name__=='__main__':main()
