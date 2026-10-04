"""Targeted 3-pair K_{2,2,2} fluid hybrid-law profit separation.

Each pair has two vertices with shared unit-heavy activation. The fluid
support is the 12-edge octahedral graph between distinct pairs, which
contains triangles and reuses both ports. Fluid is uncapped here; results
with y_e>=1/12 also apply to cap C_e>=12*y_e. This is a diagnostic only.
"""
import itertools
import numpy as np
from scipy.optimize import linprog

PAIRS=range(3)
VERTS=range(6)
EDGES=[(u,v) for u in VERTS for v in range(u+1,6) if u//2!=v//2]
NE=len(EDGES)
STATES=list(itertools.product((0,1),repeat=3))
A=np.array([[int(v in e) for e in EDGES] for v in VERTS],dtype=float)

def probs(D):
    p=(1+2*np.array(D))/3
    ind=np.array([np.prod([p[i] if s[i] else 1-p[i] for i in PAIRS]) for s in STATES])
    cuts=sorted(set([0.,1.,*p]))
    co=np.zeros(8)
    for lo,hi in zip(cuts[:-1],cuts[1:]):
        s=tuple(int((lo+hi)/2<=z) for z in p)
        co[STATES.index(s)]+=hi-lo
    return .75*ind+.25*co

def fluid_opt(q,s):
    ids=[j for j,(u,v) in enumerate(EDGES) if s[u//2] and s[v//2]]
    if not ids:return 0.,np.zeros(NE)
    sol=linprog(-q[ids],A_ub=A[:,ids],b_ub=np.ones(6),bounds=[(0,1)]*len(ids),method='highs')
    if not sol.success:raise RuntimeError(sol.message)
    pat=np.zeros(NE);pat[ids]=sol.x
    return -sol.fun,pat

def profit_oracle(D,y,limit=200):
    pp=probs(D)
    pats=[[] for _ in STATES]
    for j,(u,v) in enumerate(EDGES):
        for i,s in enumerate(STATES):
            if s[u//2] and s[v//2]:
                p=np.zeros(NE);p[j]=1;pats[i].append(p)
    for step in range(limit):
        rows=[];b=[]
        for i,group in enumerate(pats):
            for pat in group:
                row=np.zeros(NE+8);row[:NE]=pat;row[NE+i]=-1
                rows.append(row);b.append(0.)
        row=np.zeros(NE+8);row[NE:]=pp
        rows.append(row);b.append(1.)
        c=np.r_[-np.array(y),np.zeros(8)]
        sol=linprog(c,A_ub=np.array(rows),b_ub=np.array(b),bounds=[(0,None)]*(NE+8),method='highs')
        if not sol.success:raise RuntimeError(sol.message)
        q=sol.x[:NE];t=sol.x[NE:]
        added=False
        for i,s in enumerate(STATES):
            val,pat=fluid_opt(q,s)
            if val>t[i]+1e-8:
                if any(np.max(np.abs(pat-old))<1e-8 for old in pats[i]):
                    raise RuntimeError('duplicate violated pattern')
                pats[i].append(pat);added=True
        if not added:return -sol.fun,q,step
    raise RuntimeError('cutting limit')

def local_opt(D,q):
    bounds=[(0,None)]*NE
    caps=np.array([D[v//2] for v in VERTS])
    sol=linprog(-q,A_ub=A,b_ub=caps,bounds=bounds,method='highs')
    if not sol.success:raise RuntimeError(sol.message)
    return sol.x

if __name__=='__main__':
    rng=np.random.default_rng(20261004)
    best=(0,None)
    levels=[1/6,1/3,1/2,2/3,5/6,1.]
    count=0
    for D in itertools.combinations_with_replacement(levels,3):
        choices=[np.eye(NE)[i] for i in range(NE)]
        choices.extend(rng.dirichlet(np.ones(NE)*.7,size=70))
        for direction in choices:
            y=local_opt(D,direction)
            val,q,steps=profit_oracle(D,y)
            count+=1
            if val>best[0]+1e-8:
                best=(val,(D,y.tolist(),q.tolist(),steps))
                print('BEST',count,val,best[1],flush=True)
    print('FINAL',count,best,flush=True)
