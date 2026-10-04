"""Falsify a moment-only proof route; numeric output is never a proof.

The tentative uncapped probe is b = (4/3)a/(p*q). Each independent competitor
sum X has prescribed mean (4/3)(D-a)/p and a variance upper bound from the
Bernoulli construction. We relax the distribution to arbitrary grid masses.
"""
import json
from pathlib import Path
import numpy as np
from scipy.optimize import linprog

K=4/3
rng=np.random.default_rng(731)

def one_mom(a,D):
    p=(1+3*D)/4
    s=D-a
    h=lambda t:3*t*(1-t)/(1+3*t)
    var=K*K*s*h(min(s,1/3))/(p*p)
    mu=K*s/p
    xmax=4*K*s/p
    grid=np.unique(np.r_[np.linspace(0,xmax,121),mu])
    return grid,mu,mu*mu+var

def solve(a,Du,Dv,starts=3):
    pu,pv=(1+3*Du)/4,(1+3*Dv)/4
    if pu*pv<1/9: return None
    b=K*a/(pu*pv)
    x,mx,sx=one_mom(a,Du); y,my,sy=one_mom(a,Dv)
    mat=1/np.maximum(1,b+np.maximum(x[:,None],y[None,:]))
    def lp(c,g,m,s):
        return linprog(c,A_ub=[g*g],b_ub=[s],A_eq=[np.ones(len(g)),g],b_eq=[1,m],bounds=(0,None),method='highs').x
    best=None
    for seed in range(starts):
        py=lp(rng.normal(size=len(y)) if seed else np.ones(len(y)),y,my,sy)
        for i in range(25):
            px=lp(mat@py,x,mx,sx)
            pyn=lp(px@mat,y,my,sy)
            if np.max(abs(pyn-py))<1e-9:
                py=pyn;break
            py=pyn
        val=float(px@mat@py)
        if best is None or val<best['value']:
            best=dict(a=a,D=[Du,Dv],b=b,value=val,ratio=K*val,
                X=[(float(t),float(p)) for t,p in zip(x,px) if p>1e-8],
                Y=[(float(t),float(p)) for t,p in zip(y,py) if p>1e-8],
                mean=[mx,my],second=[sx,sy])
    return best

records=[]
pars=[(0.,1.,1.)]
for a in [0.,.05,.15,.25,1/3,.4,.5,.7]:
    for u in [0.,.25,.5,.75,1.]:
        for v in [0.,.25,.5,.75,1.]:
            if v>=u:pars.append((a,a+(1-a)*u,a+(1-a)*v))
for a,du,dv in pars:
    r=solve(a,du,dv)
    if r is not None:
        records.append(r)
        if r['value']<9/16-1e-8:
            print(json.dumps(r),flush=True)
Path(__file__).with_suffix('.json').write_text(json.dumps(records,indent=2))
print('NUMERIC RELAXATION MINIMUM',json.dumps(min(records,key=lambda r:r['value'])),flush=True)
