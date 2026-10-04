"""Numerical test of the paired Bernoulli fractional-matching inequality."""
import itertools
import json
from pathlib import Path
import random
import numpy as np
from scipy.optimize import linprog


def test(rng, number):
    n=rng.choice([3,4,5,6,7,8,9,10])
    pairs=[tuple(range(i,min(i+2,n))) for i in range(0,n,2)]
    D=np.array([rng.choice([.01,.05,.1,.2,.25,1/3,.4,.5,.6,2/3,.75,.8,.9,.95,1]) for _ in pairs])
    if len(pairs[-1])==1: D[-1]=1
    caps=np.zeros(n)
    for pair,d in zip(pairs,D): caps[list(pair)]=d
    edges=rng.sample(list(itertools.combinations(range(n),2)),rng.randint(n-1,min(n*(n-1)//2,2*n)))
    q=np.array([rng.choice([1,1,1,2,3,5,8]) for _ in edges])
    inc=np.zeros((n,len(edges)))
    for j,(u,v) in enumerate(edges): inc[u,j]=inc[v,j]=1
    opt=linprog(-q,A_ub=inc,b_ub=caps,bounds=(0,None))
    assert opt.success
    mean=0
    states=[]
    for bits in itertools.product([0,1],repeat=len(pairs)):
        prob=1
        cap=np.zeros(n)
        for pair,bit,d in zip(pairs,bits,D):
            p=(1+2*d)/3
            prob*=p if bit else 1-p
            cap[list(pair)]=bit
        if prob<1e-14: continue
        val=linprog(-q,A_ub=inc,b_ub=cap,bounds=(0,None))
        assert val.success
        mean-=prob*val.fun
        states.append((bits,prob,-val.fun))
    ratio=mean/(-(2/3)*opt.fun)
    if ratio<1-1e-7:
        return dict(trial=number,n=n,pairs=pairs,D=D.tolist(),F=edges,q=q.tolist(),y=opt.x.tolist(),
            target=-(2/3)*opt.fun,recourse=mean,ratio=ratio,states=states),ratio
    return None,ratio


if __name__=='__main__':
    rng=random.Random(2026100351)
    best=100
    for i in range(4000):
        result,ratio=test(rng,i)
        best=min(best,ratio)
        if result:
            Path(__file__).with_suffix('.json').write_text(json.dumps(result,indent=2))
            print(json.dumps(result),flush=True)
            break
        if i%200==199: print(f'{i+1} cases, least ratio {best:.12g}',flush=True)
    else: print(f'No counterexample in 4000 cases; least ratio {best:.12g}',flush=True)
