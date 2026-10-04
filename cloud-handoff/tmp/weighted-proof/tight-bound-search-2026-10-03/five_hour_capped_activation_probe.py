"""Numerical tests only; finite edge caps under independent vertex activation."""
import itertools, json, random, time
from pathlib import Path
import numpy as np
from scipy.optimize import linprog

rng=random.Random(20261003052117)
best={k:float('inf') for k in (4,8,12,16)}
records={}
start=time.time()
for case in range(1200):
    nleft=rng.choice([2,3,4]); nright=rng.choice([2,3,4]); n=nleft+nright
    pool=[(u,nleft+v) for u in range(nleft) for v in range(nright)]
    edges=rng.sample(pool,rng.randint(1,len(pool)))
    m=len(edges)
    A=np.zeros((n,m))
    for i,(u,v) in enumerate(edges): A[u,i]=A[v,i]=1
    q=np.array([10**rng.uniform(-1,1) for _ in edges])
    C=np.array([10**rng.uniform(-3,1.4) for _ in edges])
    D=np.array([rng.choice([0.001,0.01,.05,.1,1/3,.5,.75,1.]) for _ in range(n)])
    p=(1+3*D)/4
    mean=0.
    for bits in itertools.product((0,1),repeat=n):
        r=np.array(bits)
        pr=np.prod(np.where(r,p,1-p))
        if pr<1e-18: continue
        fit=linprog(-q,A_ub=A,b_ub=r,bounds=list(zip(np.zeros(m),C)),method='highs')
        assert fit.success
        mean-=pr*fit.fun
    for K in best:
        target=linprog(-q,A_ub=A,b_ub=D,bounds=list(zip(np.zeros(m),C/K)),method='highs')
        assert target.success
        if target.fun>=-1e-15:continue
        ratio=mean/(-.75*target.fun)
        if ratio<best[K]:
            best[K]=ratio
            records[K]=dict(case=case,n=n,edges=edges,q=q.tolist(),C=C.tolist(),D=D.tolist(),target=target.x.tolist(),actual_mean=mean,ratio=ratio)
        if K>=12 and ratio<1-1e-7:
            print('COUNTEREXAMPLE',json.dumps(records[K]),flush=True)
            Path(__file__).with_suffix('.json').write_text(json.dumps(records,indent=2))
            raise SystemExit(1)
    if (case+1)%50==0:
        print(json.dumps(dict(cases=case+1,best=best,seconds=round(time.time()-start,1))),flush=True)
        Path(__file__).with_suffix('.json').write_text(json.dumps(records,indent=2))
print('Complete; numerical evidence only.',flush=True)
