"""Numerical falsification search for shared-independent/private-correlated star overflow."""
import itertools
import random

import numpy as np
from scipy.optimize import linprog


def law_shared(ps, hub_p):
    atoms=[]
    for bits in itertools.product((0,1),repeat=len(ps)):
        mass=np.prod([p if b else 1-p for b,p in zip(bits,ps)])
        atoms.extend([(sum(bits)-1,mass*hub_p),(sum(bits),mass*(1-hub_p))])
    merged={}
    for d,m in atoms: merged[d]=merged.get(d,0)+m
    return list(merged.items())


def min_overflow(shared, cs, qs):
    private=list(itertools.product((0,1),repeat=len(cs)))
    n=len(shared)*len(private)
    obj=[]
    for d,m in shared:
        for bits in private:
            obj.append(max(0,d+sum(c*b for c,b in zip(cs,bits))))
    rows=[];rhs=[]
    for j,(d,m) in enumerate(shared):
        row=[0.]*n
        for k in range(len(private)):row[j*len(private)+k]=1
        rows.append(row);rhs.append(m)
    for i,q in enumerate(qs):
        rows.append([bits[i] for d,m in shared for bits in private]);rhs.append(q)
    result=linprog(obj,A_eq=rows,b_eq=rhs,bounds=(0,None),method='highs')
    return result.fun if result.success else None


if __name__=='__main__':
    rng=random.Random(10032026)
    best=(0,None)
    grid=[i/20 for i in range(1,20)]
    for t in range(10000):
        ns=rng.randrange(0,5)
        npv=rng.randrange(1,5)
        ps=[rng.choice(grid) for _ in range(ns)]
        cs=[rng.choice([1,2]) for _ in range(npv)]
        qs=[rng.choice(grid) for _ in range(npv)]
        x=rng.choice(grid+[1.])
        if sum(ps)+sum(c*q for c,q in zip(cs,qs))>x+1e-9:continue
        v=min_overflow(law_shared(ps,x),cs,qs)
        if v is not None and v>best[0]:
            best=(v,(ps,x,cs,qs))
            if v>.5000001:print('FAIL',best,flush=True);break
    print('BEST',best,flush=True)
