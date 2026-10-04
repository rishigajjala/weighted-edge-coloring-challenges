"""Try to refute repair while fixing an arbitrary projected matching law.

Numerical search only; any witness needs exact subsequent verification.
"""
import itertools
import json
from pathlib import Path
import random
import numpy as np
from scipy.optimize import linprog
from scipy.sparse import lil_matrix


def matchings(n, edges):
    def rec(vertices, chosen):
        if not vertices:
            yield chosen
            return
        v = min(vertices)
        yield from rec(vertices-{v}, chosen)
        for i,(a,b) in enumerate(edges):
            if v not in (a,b): continue
            u = b if a == v else a
            if u in vertices:
                yield from rec(vertices-{v,u}, chosen+[i])
    return list(rec(set(range(n)), []))


def trial(rng, number):
    n = rng.choice([5,6,7])
    pairs = list(itertools.combinations(range(n),2))
    H = rng.sample(pairs, rng.randint(n-1, min(len(pairs),n+3)))
    F = rng.sample(pairs, rng.randint(n-1, min(len(pairs),n+3)))
    w = np.array([rng.choice([.51,.55,.6,.7,.8,.9,1]) for _ in H])
    p = np.array([rng.choice([0,1,2,3,4]) for _ in H+F])
    nh,nf = len(H),len(F)
    local = np.zeros((2*n,nh+nf))
    for i,(u,v) in enumerate(H):
        local[u,i] = local[v,i] = 1
        local[n+u,i] = local[n+v,i] = w[i]
    for j,(u,v) in enumerate(F):
        local[n+u,nh+j] = local[n+v,nh+j] = 1
    loc = linprog(-p,A_ub=local,b_ub=np.ones(2*n),bounds=(0,None))
    assert loc.success
    x,y = loc.x[:nh],loc.x[nh:]
    z = (2/3)*loc.x
    ms = matchings(n,H+F)
    inc = np.zeros((nh+nf,len(ms)))
    for j,M in enumerate(ms): inc[M,j] = 1
    counts = inc[nh:].sum(axis=0)
    eq = np.vstack([np.ones(len(ms)),inc[:nh]])
    rhs = np.r_[1,z[:nh]]
    proj = linprog(-counts,A_eq=eq,b_eq=rhs,A_ub=inc[nh:],b_ub=z[nh:],bounds=(0,None))
    assert proj.success
    removed = z[nh:].sum()+proj.fun
    if removed < 1e-8: return None
    tie = np.array([rng.random() for _ in ms])
    proj2 = linprog(-tie,A_eq=np.vstack([eq,counts]),b_eq=np.r_[rhs,-proj.fun],
                    A_ub=inc[nh:],b_ub=z[nh:],bounds=(0,None))
    assert proj2.success
    law = {}
    for M,prob in zip(ms,proj2.x):
        if prob > 1e-10:
            A = tuple(e for e in M if e<nh)
            law[A] = law.get(A,0)+prob
    states = list(law)
    ns = len(states)
    ub = lil_matrix((ns*n+nf,ns*nf))
    caps = []
    for s,A in enumerate(states):
        res = np.ones(n)
        for e in A:
            for v in H[e]: res[v] -= w[e]
        caps.extend(law[A]*res)
        for f,(u,v) in enumerate(F):
            ub[s*n+u,s*nf+f] = 1
            ub[s*n+v,s*nf+f] = 1
            ub[ns*n+f,s*nf+f] = 1
    repair = linprog(-np.ones(ns*nf),A_ub=ub.tocsr(),b_ub=np.r_[caps,z[nh:]],bounds=(0,None))
    assert repair.success
    deficit = z[nh:].sum()+repair.fun
    if deficit > 1e-7:
        price = 1+repair.ineqlin.marginals[ns*n:]
        return dict(trial=number,n=n,H=H,F=F,w=w.tolist(),p=p.tolist(),
                    x=x.tolist(),y=y.tolist(),removed=removed,deficit=deficit,
                    heavy_law=[[list(A),law[A]] for A in states],
                    unit_law=[[M,float(v)] for M,v in zip(ms,proj2.x) if v>1e-10],
                    projected=(inc@proj2.x).tolist(), fluid_price=price.tolist())
    return None


if __name__ == '__main__':
    rng = random.Random(2026100319)
    for i in range(5000):
        result = trial(rng,i)
        if result:
            Path(__file__).with_suffix('.json').write_text(json.dumps(result,indent=2))
            print(json.dumps(result),flush=True)
            break
        if i%200 == 199: print('passed',i+1,flush=True)
    else: print('No failure in 5000 trials.',flush=True)
