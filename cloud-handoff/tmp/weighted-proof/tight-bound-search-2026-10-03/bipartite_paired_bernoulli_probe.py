"""Test a 3/4 recourse inequality on bipartite union support.

Unlike earlier random tests, retain only fluid edges used by a chosen
target optimum, and test arbitrary capacities rather than local vertices.
Numerical tests do not prove the proposed inequality.
"""
import itertools
import json
from pathlib import Path
import random
import numpy as np
from scipy.optimize import linprog


def test(rng, number):
    m=rng.choice([2,3,4,5,6])
    n=2*m
    pairs=[(i,m+i) for i in range(m)]
    D=np.array([rng.choice([.01,.05,.1,.2,.25,1/3,.4,.5,.6,2/3,.75,.8,.9,.95,1]) for _ in pairs])
    caps=np.r_[D,D]
    edges=rng.sample([(i,m+j) for i in range(m) for j in range(m)],rng.randint(1,min(m*m,3*m)))
    q=np.array([rng.choice([1,1,1,2,3,5,8]) for _ in edges])
    inc=np.zeros((n,len(edges)))
    for j,(u,v) in enumerate(edges): inc[u,j]=inc[v,j]=1
    opt=linprog(-q,A_ub=inc,b_ub=caps,bounds=(0,None))
    assert opt.success
    keep=np.flatnonzero(opt.x>1e-9)
    edges=[edges[j] for j in keep]
    y=opt.x[keep]
    q=q[keep]
    inc=inc[:,keep]
    mean=0
    states=[]
    for bits in itertools.product([0,1],repeat=len(pairs)):
        prob=1
        cap=np.zeros(n)
        for pair,bit,d in zip(pairs,bits,D):
            p=(1+3*d)/4
            prob*=p if bit else 1-p
            cap[list(pair)]=bit
        if prob<1e-14: continue
        val=linprog(-q,A_ub=inc,b_ub=cap,bounds=(0,None))
        assert val.success
        mean-=prob*val.fun
        states.append((bits,prob,-val.fun))
    ratio=mean/(-.75*opt.fun)
    if ratio<1-1e-7:
        return dict(trial=number,n=n,pairs=pairs,D=D.tolist(),F=edges,q=q.tolist(),y=y.tolist(),
            target=-.75*opt.fun,recourse=mean,ratio=ratio,states=states),ratio
    return None,ratio


if __name__=='__main__':
    rng=random.Random(2026100357)
    best=100
    for i in range(5000):
        result,ratio=test(rng,i)
        best=min(best,ratio)
        if result:
            Path(__file__).with_suffix('.json').write_text(json.dumps(result,indent=2))
            print(json.dumps(result),flush=True)
            break
        if i%200==199: print(f'{i+1} cases, least ratio {best:.12g}',flush=True)
    else: print(f'No counterexample in 5000 cases; least ratio {best:.12g}',flush=True)
