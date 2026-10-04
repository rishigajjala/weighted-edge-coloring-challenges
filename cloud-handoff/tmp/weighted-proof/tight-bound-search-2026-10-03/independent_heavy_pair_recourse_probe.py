"""Test independent categorical heavy pairs against full fluid recourse.

Numerical evidence only; any failure requires exact verification.
"""
import itertools
import json
from pathlib import Path
import random
import numpy as np
from scipy.optimize import linprog


def trial(rng, trial_id):
    n = rng.choice([5, 6, 8, 10])
    verts = list(range(n))
    rng.shuffle(verts)
    pairs = list(zip(verts[::2], verts[1::2]))
    H, W, groups = [], [], []
    for u,v in pairs:
        group = []
        for _ in range(rng.randint(1,3)):
            group.append(len(H))
            H.append((u,v))
            W.append(rng.choice([.5001,.51,.6,.7,.8,.9,1]))
        groups.append(group)
    F = rng.sample(list(itertools.combinations(range(n),2)), rng.randint(n-1,min(n*(n-1)//2,2*n)))
    nh,nf = len(H),len(F)
    p = np.array([rng.choice([0,1,2,3,4,8]) for _ in H+F])
    matrix = np.zeros((n+len(groups),nh+nf))
    fluid_inc = np.zeros((n,nf))
    for i,(u,v) in enumerate(H): matrix[u,i]=matrix[v,i]=W[i]
    for j,(u,v) in enumerate(F):
        matrix[u,nh+j]=matrix[v,nh+j]=1
        fluid_inc[u,j]=fluid_inc[v,j]=1
    for j,group in enumerate(groups): matrix[n+j,group]=1
    local = linprog(-p,A_ub=matrix,b_ub=np.ones(n+len(groups)),bounds=(0,None))
    assert local.success
    x,y = local.x[:nh],local.x[nh:]
    if y.sum()<1e-8: return None, None
    fi = np.flatnonzero(y>1e-9)
    F = [F[j] for j in fi]
    fluid_inc = fluid_inc[:,fi]
    y = y[fi]
    q0 = p[nh:][fi]
    laws = []
    for group in groups:
        states = [(e,(2/3)*x[e]) for e in group if x[e]>1e-9]
        states.append((None,1-sum(prob for e,prob in states)))
        laws.append(states)
    ratios=[]
    for rep in range(3):
        q = q0 if rep==0 else np.array([rng.choice([0,1,2,3,4,8]) for _ in F])
        target=(2/3)*(q@y)
        if target <1e-8: continue
        recourse=0
        for choices in itertools.product(*laws):
            prob=1
            cap=np.ones(n)
            for e,pe in choices:
                prob*=pe
                if e is not None:
                    for v in H[e]: cap[v]-=W[e]
            lp=linprog(-q,A_ub=fluid_inc,b_ub=cap,bounds=(0,None))
            assert lp.success
            recourse-=prob*lp.fun
        ratios.append(recourse/target)
        if recourse+1e-7<target:
            return dict(trial=trial_id,n=n,H=H,F=F,w=W,groups=groups,x=x.tolist(),y=y.tolist(),
                p=p.tolist(),q=q.tolist(),target=target,recourse=recourse,ratio=recourse/target),min(ratios)
    return None,min(ratios,default=None)


if __name__=='__main__':
    rng=random.Random(2026100347)
    minimum=100
    for i in range(3000):
        result,ratio=trial(rng,i)
        if ratio is not None: minimum=min(minimum,ratio)
        if result:
            Path(__file__).with_suffix('.json').write_text(json.dumps(result,indent=2))
            print(json.dumps(result),flush=True)
            break
        if i%100==99: print(f'{i+1} passed, least ratio {minimum:.12g}',flush=True)
    else: print(f'No failure in 3000 instances; least ratio {minimum:.12g}',flush=True)
