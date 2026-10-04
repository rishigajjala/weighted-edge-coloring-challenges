"""Targeted exact-state profit oracle for revised 3/4-product, 1/4-comonotone law.

Three unit-heavy pairs have endpoints L_i,R_i. Fluid is the six-edge
bipartite graph L_i--R_j for i!=j, a C6. This probe only uses y_e=0 or
y_e>=1/12, so cap 12*y_e gives full unit capacity on retained edges.
The LP optimizes ALL nonnegative fluid profits for each fixed (D,y).
"""
import itertools
import numpy as np
from scipy.optimize import linprog
from scipy.spatial import HalfspaceIntersection

ALPHA=2/3
EDGES=[(i,j) for i in range(3) for j in range(3) if i!=j]
STATES=list(itertools.product((0,1), repeat=3)) # 1 means pair free

def matchings(edges):
    pats=[]
    for mask in range(1<<len(edges)):
        chosen=[k for k in range(len(edges)) if mask>>k&1]
        if len({edges[k][0] for k in chosen})<len(chosen):continue
        if len({edges[k][1] for k in chosen})<len(chosen):continue
        pats.append(np.array([(mask>>k)&1 for k in range(len(edges))]))
    return np.array(pats,dtype=float)

PATS=[matchings([EDGES[i] for i in range(6) if s[EDGES[i][0]] and s[EDGES[i][1]]]) for s in STATES]
INDICES=[[i for i in range(6) if s[EDGES[i][0]] and s[EDGES[i][1]]] for s in STATES]
ALLP=[]
for s,indices in zip(STATES,INDICES):
    p=[]
    for row in matchings([EDGES[i] for i in indices]):
        full=np.zeros(6)
        full[indices]=row
        p.append(full)
    ALLP.append(np.array(p))

def probs(D):
    p=(1+2*np.asarray(D))/3
    independent=[]
    for s in STATES:
        independent.append(np.prod([p[i] if s[i] else 1-p[i] for i in range(3)]))
    # common U, pair i free when U<=p_i
    common=[]
    cuts=sorted(set([0.,1.,*p]))
    for s in STATES:
        val=0.
        for a,b in zip(cuts[:-1],cuts[1:]):
            mid=(a+b)/2
            if tuple(int(mid<=p[i]) for i in range(3))==s:val+=b-a
        common.append(val)
    return .75*np.array(independent)+.25*np.array(common)

def optimize_profits(D,y):
    pp=probs(D)
    # q_e>=0 and t_s>=q(P) for every matching P of state s.
    # Maximize q.y with E[t_s]<=1.
    rows=[]; rhs=[]
    for i,pats in enumerate(ALLP):
        for pat in pats:
            row=np.zeros(14);row[:6]=pat;row[6+i]=-1
            rows.append(row);rhs.append(0.)
    row=np.zeros(14);row[6:]=pp
    rows.append(row);rhs.append(1.)
    c=np.r_[-np.asarray(y),np.zeros(8)]
    sol=linprog(c,A_ub=np.array(rows),b_ub=np.array(rhs),bounds=[(0,None)]*14,method='highs')
    if not sol.success:raise RuntimeError(sol.message)
    return -sol.fun,sol.x[:6]

def valid(D,y):
    if any(0<z<1/12-1e-9 for z in y):return False
    for i in range(3):
        if sum(y[k] for k,(a,b) in enumerate(EDGES) if a==i)>D[i]+1e-9:return False
        if sum(y[k] for k,(a,b) in enumerate(EDGES) if b==i)>D[i]+1e-9:return False
    return True

if __name__=='__main__':
    rng=np.random.default_rng(20261004)
    best=(0,None)
    YGRID=np.array([0,1/12,1/6,1/4,1/3,5/12,1/2,2/3,3/4,1.])
    DGRID=np.array([1/6,1/3,1/2,2/3,5/6,1.])
    for j in range(20000):
        D=rng.choice(DGRID,size=3)
        y=rng.choice(YGRID,size=6)
        if not valid(D,y) or not np.any(y):continue
        val,q=optimize_profits(D,y)
        if val>best[0]+1e-8:
            best=(val,(D.tolist(),y.tolist(),q.tolist(),j))
            print('BEST',val,best[1],flush=True)
    print('FINAL',best,flush=True)

def local_vertices(D):
    A=[];b=[]
    for i in range(3):
        for side in (0,1):
            row=np.array([int(edge[side]==i) for edge in EDGES],dtype=float)
            A.append(row);b.append(D[i])
    for j in range(6):
        row=np.zeros(6);row[j]=-1
        A.append(row);b.append(0.)
    A=np.array(A);b=np.array(b)
    interior=np.ones(6)*min(D)/4
    hs=np.c_[A,-b]
    vertices=HalfspaceIntersection(hs,interior).intersections
    return np.unique(np.round(vertices,10),axis=0)

def exact_local_scan():
    vals=[1/6,1/3,1/2,2/3,5/6,1.]
    best=(0,None)
    count=0
    for D in itertools.combinations_with_replacement(vals,3):
        for y in local_vertices(D):
            if np.max(y)<1e-10:continue
            val,q=optimize_profits(D,y)
            count+=1
            if val>best[0]+1e-8:
                best=(val,(D,y.tolist(),q.tolist()))
                print('EXACT-BEST',val,best[1],flush=True)
    print('EXACT-FINAL',count,best,flush=True)

if __name__=='__main__':exact_local_scan()
