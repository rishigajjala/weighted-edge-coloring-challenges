"""Numerical diagnostic for the proposed 3/4 independent-vertex activation lemma.

Searches random weighted trees; a witness needs exact arithmetic verification.
"""
import json
import random
from pathlib import Path
import numpy as np
from scipy.optimize import linprog


def random_tree(rng, n):
    prufer = [rng.randrange(n) for _ in range(n-2)]
    degree = [1]*n
    for v in prufer:
        degree[v] += 1
    edges = []
    for v in prufer:
        leaf = min(i for i in range(n) if degree[i] == 1)
        edges.append((leaf, v))
        degree[leaf] -= 1
        degree[v] -= 1
    leaves = [i for i in range(n) if degree[i] == 1]
    edges.append(tuple(leaves))
    return edges


def induced_matching_values(n, edges, q):
    incident = [[] for _ in range(n)]
    for (u,v), weight in zip(edges,q):
        incident[u].append((v,weight))
        incident[v].append((u,weight))
    value = np.zeros(1<<n)
    for mask in range(1,1<<n):
        u = (mask & -mask).bit_length()-1
        rest = mask & ~(1<<u)
        best = value[rest]
        for v,weight in incident[u]:
            if rest & (1<<v):
                best = max(best, weight + value[rest & ~(1<<v)])
        value[mask] = best
    return value


def trial(rng, it):
    n = rng.randrange(4,9)
    edges = random_tree(rng,n)
    m = len(edges)
    dset = [0,1/12,1/6,1/4,1/3,2/5,1/2,3/5,2/3,3/4,5/6,1]
    D = np.array([rng.choice(dset) for _ in range(n)])
    q = np.array([rng.choice([0,1,1,1,2,3,5,8]) for _ in range(m)],dtype=float)
    inc = np.zeros((n,m))
    for i,(u,v) in enumerate(edges):
        inc[u,i]=inc[v,i]=1
    frac = linprog(-q,A_ub=inc,b_ub=D,bounds=(0,None))
    assert frac.success
    F=-frac.fun
    if F<1e-10:
        return None
    p=(1+3*D)/4
    matchvals=induced_matching_values(n,edges,q)
    prob=np.ones(1<<n)
    for mask in range(1<<n):
        for v in range(n):
            prob[mask]*=p[v] if mask & (1<<v) else 1-p[v]
    expectation=float(np.dot(prob,matchvals))
    ratio=expectation/F
    return dict(it=it,n=n,edges=edges,D=D.tolist(),q=q.tolist(),F=F,
                expectation=expectation,ratio=ratio,y=frac.x.tolist())


if __name__ == '__main__':
    rng=random.Random(2026100354)
    best=None
    for it in range(20000):
        x=trial(rng,it)
        if x is None:
            continue
        if best is None or x['ratio']<best['ratio']:
            best=x
            if it%1000==0 or x['ratio']<0.75000001:
                print('best',it,x['ratio'],flush=True)
        if x['ratio']<0.74999999:
            break
    path=Path(__file__).with_suffix('.json')
    path.write_text(json.dumps(best,indent=2))
    print(json.dumps(best),flush=True)
