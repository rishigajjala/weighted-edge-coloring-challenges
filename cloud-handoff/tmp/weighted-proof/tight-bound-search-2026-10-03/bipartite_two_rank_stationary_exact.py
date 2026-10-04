"""Enumerate all local balance vertices and optimize their stationary gauge.

For a fixed local mean vector x, its best nonnegative profit p normalized
by global stationary maximum <=1 is an LP with cycle potentials. Thus
enumerating local LP vertices gives the exact local/global ratio for the
finite transition model in bipartite_two_rank_stationary.py.
"""
import itertools
import json

import numpy as np
from scipy.optimize import linprog

import bipartite_two_rank_stationary as model


def local_vertices():
    out={}
    n=len(model.STATES)
    for k in (1,2,3):
        for support in itertools.combinations(range(n),k):
            a=model.LOCAL_EQ[:,support]
            if np.linalg.matrix_rank(a, tol=1e-9)<k:
                continue
            lam=np.linalg.lstsq(a,model.LOCAL_RHS,rcond=None)[0]
            if np.max(np.abs(a@lam-model.LOCAL_RHS))>1e-9 or min(lam)<-1e-9:
                continue
            x=lam@model.P[list(support),:]
            key=tuple(np.round(x,10))
            out.setdefault(key,(x,support,lam))
    return list(out.values())


def gauge(x):
    nn=len(model.NODES)
    ns=len(model.STATES)
    a=np.zeros((ns,4+nn-1))
    a[:,:4]=model.P
    for j,s in enumerate(model.STATES):
        src=model.NODE_INDEX[(s[0],s[1])]
        dst=model.NODE_INDEX[(s[2],s[3])]
        if src:a[j,4+src-1]-=1
        if dst:a[j,4+dst-1]+=1
    c=np.zeros(a.shape[1]);c[:4]=-x
    result=linprog(c,A_ub=a,b_ub=np.ones(ns),
                   bounds=[(0,None)]*4+[(None,None)]*(nn-1),method='highs')
    if not result.success:raise RuntimeError(result.message)
    return -result.fun,result.x[:4]


def main():
    vertices=local_vertices()
    best=(0,None)
    for i,(x,support,lam) in enumerate(vertices):
        ratio,p=gauge(x)
        if ratio>best[0]+1e-8:
            best=(ratio,{'ratio':ratio,'profit':p.tolist(),
                         'local_mean':x.tolist(),
                         'support':[(model.STATES[j],float(t)) for j,t in zip(support,lam)]})
            print('BEST',json.dumps(best[1]),flush=True)
    print('FINAL',json.dumps({'local_vertices':len(vertices),'best':best[1]}),flush=True)


if __name__=='__main__':main()
