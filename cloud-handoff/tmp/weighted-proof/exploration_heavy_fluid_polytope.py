"""Bounded diagnostic for 2/3 inclusion in heavy matching + divisible fluid."""
import itertools
import json
import random
from pathlib import Path
import numpy as np
from scipy.optimize import linprog
from scipy.sparse import coo_matrix

SEED=1702341
OUT=Path(__file__).with_suffix('.json')

def matching_list(n,H):
    out=[]
    for mask in range(1<<len(H)):
        chosen=[i for i in range(len(H)) if mask>>i&1]
        seen=set();ok=True
        for i in chosen:
            u,v=H[i]
            if u in seen or v in seen:ok=False;break
            seen.add(u);seen.add(v)
        if ok:out.append(chosen)
    return out

def local_opt(n,H,F,w,p,q):
    nh=len(H);nf=len(F)
    A=[];b=[]
    for v in range(n):
        row=np.zeros(nh+nf)
        for i,e in enumerate(H):
            if v in e:row[i]=1
        A.append(row);b.append(1)
        row=np.zeros(nh+nf)
        for i,e in enumerate(H):
            if v in e:row[i]=w[i]
        for j,e in enumerate(F):
            if v in e:row[nh+j]=1
        A.append(row);b.append(1)
    obj=-np.r_[p,q]
    res=linprog(obj,A_ub=np.array(A),b_ub=np.array(b),bounds=(0,None),method='highs')
    if not res.success:raise RuntimeError(res.message)
    return res.x,-res.fun

def scaled_feasible(n,H,F,w,x,scale=2/3):
    # Variables lambda_M and y_(M,f). For each M, incident fluid amount
    # cannot exceed lambda_M times that matching's residual capacity.
    M=matching_list(n,H);nm=len(M);nf=len(F);nh=len(H)
    nv=nm+nm*nf
    rows=[];cols=[];vals=[];rhs=[]
    row=0
    rows.extend([row]*nm);cols.extend(range(nm));vals.extend([1.]*nm)
    rhs.append(1.);row+=1
    for i in range(nh):
        for k,mm in enumerate(M):
            if i in mm:rows.append(row);cols.append(k);vals.append(1.)
        rhs.append(scale*x[i]);row+=1
    for j in range(nf):
        for k in range(nm):
            rows.append(row);cols.append(nm+k*nf+j);vals.append(1.)
        rhs.append(scale*x[nh+j]);row+=1
    Aeq=coo_matrix((vals,(rows,cols)),shape=(row,nv)).tocsr()
    Aub=[];bub=[]
    for k,mm in enumerate(M):
        for v in range(n):
            c=1-sum(w[i] for i in mm if v in H[i])
            rr=np.zeros(nv);rr[k]=-c
            for j,e in enumerate(F):
                if v in e:rr[nm+k*nf+j]=1
            Aub.append(rr);bub.append(0.)
    res=linprog(np.zeros(nv),A_eq=Aeq,b_eq=rhs,A_ub=np.array(Aub),b_ub=bub,
                bounds=(0,None),method='highs')
    return res.success,len(M)

def stream(rng):
    all5=[(u,v) for u in range(5) for v in range(u+1,5)]
    # Dense small cores with fluid on all or selected pairs.
    for k in range(250):
        H=rng.sample(all5,rng.choice([5,6,7,8]))
        F=all5 if k%3==0 else rng.sample(all5,rng.choice([5,6,7,8]))
        w=[rng.choice([.55,.6,.7,.8,.9,1.]) for _ in H]
        yield 5,H,F,w,f'dense-{k}'
    # Triangle with arbitrary fluid chords or private spokes.
    for k in range(100):
        H=[(0,1),(1,2),(0,2)]
        F=rng.sample(all5,rng.choice([4,5,6,7,8]))
        w=[rng.choice([.55,.6,.7,.8,.9,1.]) for _ in H]
        yield 5,H,F,w,f'triangle-{k}'

def main():
    rng=random.Random(SEED);checked=0;max_gap=0
    for n,H,F,w,name in stream(rng):
        for t in range(6):
            p=np.array([rng.uniform(.1,2) for _ in H]);q=np.array([rng.uniform(.1,2) for _ in F])
            x,L=local_opt(n,H,F,w,p,q)
            ok,nm=scaled_feasible(n,H,F,w,x)
            checked+=1
            if not ok:
                obj=dict(name=name,n=n,H=H,F=F,weights=w,heavy_profit=p.tolist(),
                         fluid_density=q.tolist(),x=x.tolist(),L=float(L),matchings=nm)
                OUT.write_text(json.dumps(dict(seed=SEED,checked=checked,candidate=obj),indent=2))
                print('CANDIDATE',obj,flush=True)
                return
    OUT.write_text(json.dumps(dict(seed=SEED,checked=checked,candidate=None),indent=2))
    print('finished checked',checked,'no inclusion failure')

if __name__=='__main__':main()
