"""Exact-state LP probes for alpha=4/5, cap=4y with unit heavy edges.

For small bipartite graphs, enumerate every matching of heavy support and
optimize tiny fractional recourse in that state. This is numerical evidence,
not a proof of the unrestricted smoothing lemma.
"""

import argparse
from functools import lru_cache

import numpy as np
from scipy.optimize import linprog
from scipy.sparse import coo_matrix


@lru_cache(None)
def matchings(n, heavy):
    heavy = tuple(heavy)
    out = [()]
    for e, (u, v) in enumerate(heavy):
        out += [m + (e,) for m in list(out)
                if all(heavy[j][0] != u and heavy[j][1] != v for j in m)]
    return tuple(out)


def solve(n, heavy, tiny, x, y, alpha=.8, capscale=4):
    states = matchings(n, tuple(heavy))
    ns, ne = len(states), len(tiny)
    nvar = ns * (ne + 1) + 1
    beta = nvar - 1
    def z(s, e): return ns + s * ne + e
    eq_i, eq_j, eq_v, beq = [], [], [], [1.]
    for s in range(ns):
        eq_i.append(0); eq_j.append(s); eq_v.append(1.)
    for h in range(len(heavy)):
        for s, state in enumerate(states):
            if h in state:
                eq_i.append(h + 1); eq_j.append(s); eq_v.append(1.)
        beq.append(alpha * x[h])
    n_eq = len(beq)
    ub_i, ub_j, ub_v, bub = [], [], [], []
    def addrow(items, rhs):
        r = len(bub)
        for col, val in items:
            ub_i.append(r); ub_j.append(col); ub_v.append(val)
        bub.append(rhs)
    for s, state in enumerate(states):
        occupied_u = {heavy[j][0] for j in state}
        occupied_v = {heavy[j][1] for j in state}
        for e, (u, v) in enumerate(tiny):
            addrow([(z(s,e), 1.), (s, -capscale * y[e])], 0.)
        for u in range(n):
            terms = [(z(s,e), 1.) for e, (a,b) in enumerate(tiny) if a == u]
            if u not in occupied_u: terms.append((s,-1.))
            addrow(terms, 0.)
        for v in range(n):
            terms = [(z(s,e), 1.) for e, (a,b) in enumerate(tiny) if b == v]
            if v not in occupied_v: terms.append((s,-1.))
            addrow(terms, 0.)
    for e in range(ne):
        addrow([(z(s,e),-1.) for s in range(ns)] + [(beta,y[e])], 0.)
    Aeq = coo_matrix((eq_v,(eq_i,eq_j)),shape=(n_eq,nvar)).tocsr()
    Aub = coo_matrix((ub_v,(ub_i,ub_j)),shape=(len(bub),nvar)).tocsr()
    obj = np.zeros(nvar); obj[beta] = -1.
    result = linprog(obj,A_ub=Aub,b_ub=bub,A_eq=Aeq,b_eq=beq,
                     bounds=(0,None),method="highs")
    return (-result.fun if result.success else np.nan), result.message, ns


def random_instance(n, rng):
    hmask = rng.random((n,n)) < rng.uniform(.25,.8)
    if not hmask.any(): hmask[rng.integers(n),rng.integers(n)] = True
    X = rng.exponential(size=(n,n)) * hmask
    Y = rng.exponential(size=(n,n))
    Y *= rng.random((n,n)) < rng.uniform(.3,1.)
    if not Y.any(): Y[rng.integers(n),rng.integers(n)] = 1.
    # Deliberately vary heavy-versus-tiny load and proximity to saturation.
    X *= rng.uniform(.1,2.); Y *= rng.uniform(.1,2.)
    T = X+Y
    for _ in range(10):
        Trows=T.sum(axis=1)
        scale=np.minimum(1.,1./np.maximum(Trows,1e-12))
        X*=scale[:,None];Y*=scale[:,None];T=X+Y
        Tcols=T.sum(axis=0)
        scale=np.minimum(1.,1./np.maximum(Tcols,1e-12))
        X*=scale[None,:];Y*=scale[None,:];T=X+Y
    heavy=[(i,j) for i in range(n) for j in range(n) if X[i,j]>1e-9]
    tiny=[(i,j) for i in range(n) for j in range(n) if Y[i,j]>1e-9]
    x=np.array([X[e] for e in heavy]);y=np.array([Y[e] for e in tiny])
    return heavy,tiny,x,y


def main():
    p=argparse.ArgumentParser()
    p.add_argument('--n',type=int,default=3)
    p.add_argument('--trials',type=int,default=1000)
    p.add_argument('--seed',type=int,default=9396)
    args=p.parse_args();rng=np.random.default_rng(args.seed)
    best=(float('inf'),None)
    for t in range(args.trials):
        heavy,tiny,x,y=random_instance(args.n,rng)
        b,msg,ns=solve(args.n,heavy,tiny,x,y)
        if b<best[0]:
            best=(b,(heavy,tiny,x,y,ns))
            print('newmin',t,'beta',b,'states',ns,flush=True)
        if np.isnan(b) or b < .8-1e-7:
            print('FAIL',t,'beta',b,'message',msg,'data',best[1],flush=True)
            return
    print('all',args.trials,'min_beta',best[0],'instance',best[1],flush=True)


if __name__=='__main__': main()
