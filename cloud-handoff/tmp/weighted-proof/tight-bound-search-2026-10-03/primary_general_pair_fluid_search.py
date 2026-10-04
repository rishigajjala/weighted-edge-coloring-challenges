"""Numerical search for failure of paired-capacity fluid half deficit.
Every state flow is divisible, without individual edge supply caps.
This is exploration, not a proof.
"""
import itertools, json, time
from pathlib import Path
import numpy as np
from scipy.optimize import linprog
from scipy.sparse import lil_matrix

SEED=31026003
rng=np.random.default_rng(SEED)
OUT=Path(__file__).with_suffix('.json')

def check(n, k, edges, low, high, prob, q):
    m=len(edges)
    inc=np.array([[float(v in e) for e in edges] for v in range(n)])
    mean=np.ones(n)
    mean[:2*k]=np.repeat(low+(high-low)*prob,2)
    def flowval(cap):
        r=linprog(-q,A_ub=inc,b_ub=cap,bounds=(0,None),method='highs')
        assert r.success,r.message
        return -r.fun,r.x
    local,y=flowval(mean)
    full,_=flowval(np.ones(n))
    states=np.array(list(itertools.product([0,1],repeat=k)))
    s=len(states)
    # p[state], f[state,edge], where f is probability times flow.
    eq=np.zeros((k+1,s*(m+1)))
    eq[0,:s]=1
    eq[1:,:s]=states.T
    ub=lil_matrix((s*n,s*(m+1)))
    for j,state in enumerate(states):
        cap=np.ones(n)
        cap[:2*k]=np.repeat(low+(high-low)*state,2)
        ub[j*n:(j+1)*n,j]=-cap[:,None]
        ub[j*n:(j+1)*n,s+j*m:s+(j+1)*m]=inc
    obj=np.r_[np.zeros(s),np.tile(-q,s)]
    r=linprog(obj,A_ub=ub.tocsr(),b_ub=np.zeros(s*n),
              A_eq=eq,b_eq=np.r_[1,prob],bounds=(0,None),method='highs')
    assert r.success,r.message
    return (local+r.fun)/full,dict(n=n,k=k,edges=edges,low=low.tolist(),
        high=high.tolist(),prob=prob.tolist(),q=q.tolist(),local=local,
        expected=-r.fun,full=full,mean_flow=y.tolist(),coupling=r.x[:s].tolist())

def main():
    start=time.monotonic()
    best={'gap':-1}
    count=0
    for trial in range(5000):
        k=int(rng.choice([3,4]))
        n=2*k+int(rng.choice([0,1,2]))
        mode=trial%4
        edges=[(u,v) for u in range(n) for v in range(u+1,n)
               if rng.random() < (0.35 if mode else 0.8)]
        if not edges: continue
        low=rng.choice([0,.1,.2,.3,.4,.5,.6,.7],k).astype(float)
        high=low+(1-low)*rng.choice([.25,.5,.75,1],k)
        prob=rng.choice([.1,.2,.3,.4,.5,.6,.7,.8,.9],k)
        q=rng.choice([.25,.5,.75,1,1.5,2],len(edges))
        gap,record=check(n,k,edges,low,high,prob,q)
        count+=1
        if gap>best['gap']+1e-10:
            best={'gap':float(gap),**record}
            print('BEST',count,round(gap,12),flush=True)
            OUT.write_text(json.dumps(dict(seed=SEED,count=count,best=best,finished=False),indent=2))
        if gap>.50000001:break
        if trial%250==0: print('PROGRESS',trial,round(time.monotonic()-start,1),flush=True)
    OUT.write_text(json.dumps(dict(seed=SEED,count=count,best=best,finished=True,
        seconds=time.monotonic()-start),indent=2))
    print('DONE',count,best['gap'],flush=True)
if __name__=='__main__':main()
