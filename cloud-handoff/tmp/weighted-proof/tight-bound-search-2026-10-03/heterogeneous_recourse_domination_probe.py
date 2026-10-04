"""Target the stronger weighted-heavy mean-activation domination conjecture.
Numerical tests only. All LPs are finite, but sampled input is nonexhaustive.
"""
import itertools,json,random,time
from pathlib import Path
import numpy as np
from scipy.optimize import linprog
rng=random.Random(202610030553)
best=100.
records=[]
for trial in range(5000):
    k=rng.choice([2,2,3]); n=2*k+2
    H=[(u,k+v) for u in range(k) for v in range(k)]
    mats=[]
    for mask in range(1<<len(H)):
        inds=[i for i in range(len(H)) if mask>>i&1]
        flat=[v for i in inds for v in H[i]]
        if len(flat)==len(set(flat)):
            a=np.zeros(len(H));a[inds]=1;mats.append(a)
    mats=np.array(mats)
    perfect=mats[mats.sum(axis=1)==k]
    weights=np.array([rng.choice([.5001,.51,.6,.75,.9,1.]) for _ in H])
    convex=np.array([rng.expovariate(1) for _ in perfect]);convex/=convex.sum()
    alpha=rng.choice([.75,.75,.75,1.])
    t=alpha*convex.dot(perfect)
    Fpool=[(u,v) for u in list(range(k))+[2*k] for v in list(range(k,2*k))+[2*k+1]]
    F=rng.sample(Fpool,rng.randint(1,len(Fpool)))
    q=np.array([rng.choice([1.,1.,2.,3.,5.,8.]) for _ in F])
    inc=np.zeros((n,len(F)))
    for i,(u,v) in enumerate(F):inc[u,i]=inc[v,i]=1
    hinc=np.zeros((n,len(H)))
    for i,(u,v) in enumerate(H):hinc[u,i]=hinc[v,i]=1
    p=1-hinc.dot(weights*t)
    mean=0.
    for bits in itertools.product((0,1),repeat=2*k):
        r=np.ones(n);r[:2*k]=bits
        pr=np.prod(np.where(r[:2*k],p[:2*k],1-p[:2*k]))
        if pr<1e-15:continue
        res=linprog(-q,A_ub=inc,b_ub=r,bounds=(0,None))
        assert res.success
        mean-=pr*res.fun
    vals=[]
    for a in mats:
        r=1-hinc.dot(weights*a)
        res=linprog(-q,A_ub=inc,b_ub=r,bounds=(0,None))
        assert res.success
        vals.append(-res.fun)
    fit=linprog(-np.array(vals),A_eq=np.vstack((np.ones(len(mats)),mats.T)),b_eq=np.r_[1,t],bounds=(0,None))
    assert fit.success
    ratio=-fit.fun/mean if mean else 1.
    best=min(best,ratio)
    if ratio<1-1e-7:
        rec=dict(trial=trial,alpha=alpha,H=H,F=F,q=q.tolist(),w=weights.tolist(),t=t.tolist(),p=p.tolist(),product_recourse=mean,best_actual_recourse=-fit.fun,ratio=ratio,law=[(mats[i].tolist(),float(v),vals[i]) for i,v in enumerate(fit.x) if v>1e-8])
        records.append(rec)
        print('FAIL',json.dumps(rec),flush=True)
        Path(__file__).with_suffix('.json').write_text(json.dumps(records,indent=2))
        if alpha==.75:break
    if (trial+1)%200==0:print('Progress',trial+1,'least ratio',best,flush=True)
else: print('Complete; no alpha=.75 violation in 5000 sampled instances.',flush=True)
