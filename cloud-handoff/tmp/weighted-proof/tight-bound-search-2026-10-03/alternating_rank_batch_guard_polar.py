"""Enumerate every stationary-profit polar vertex of the 0.34/0.26
two-period batch-reversal guard template.  Exact template, floating
geometry/LP diagnostics; no coloring theorem is asserted.
"""
import collections
import numpy as np
from scipy.spatial import HalfspaceIntersection
from alternating_rank_batch_guard_stationary import states, Q, offs, solve

arcs=collections.defaultdict(list)
for i in range(2):
    for j,(a,b,g) in enumerate(states[i]):
        src=(1-i,a) if i==0 else (0,a)  # i=0: B->A; i=1: A->B
        dst=(0,b) if i==0 else (1,b)
        arcs[src].append((dst,offs[i]+j))
nodes=list(arcs)
cycles=set()
for start in nodes:
    def dfs(u,seen,path):
        for v,edge in arcs[u]:
            if v==start and path:
                cyc=path+(edge,)
                rots=[cyc[k:]+cyc[:k] for k in range(len(cyc))]
                cycles.add(min(rots))
            elif v not in seen and len(path)<len(nodes):
                dfs(v,seen|{v},path+(edge,))
    dfs(start,{start},())

patterns=[]
for cyc in cycles:
    t=len(cyc)//2
    patterns.append(Q[:,list(cyc)].sum(axis=1)/t)
patterns=np.unique(np.round(np.array(patterns),12),axis=0)
# A coordinatewise dominated pattern can never define a tight polar facet.
keep=np.ones(len(patterns),dtype=bool)
for i,p in enumerate(patterns):
    if any(np.all(q>=p-1e-10) and np.any(q>p+1e-10) for j,q in enumerate(patterns) if i!=j):
        keep[i]=False
P=patterns[keep]
hs=np.vstack([np.c_[P,-np.ones(len(P))],np.c_[-np.eye(4),np.zeros(4)]])
q0=np.full(4,0.1/max(1,np.max(P.sum(axis=1))))
assert np.max(hs[:,:4]@q0+hs[:,4])<-1e-10
verts=HalfspaceIntersection(hs,q0,qhull_options="QJ").intersections
verts=np.unique(np.round(verts,10),axis=0)
best=(-1,None)
for q in verts:
    if np.min(q)<-1e-7 or np.max(P@q)>1+1e-7: continue
    local,x=solve(q)
    global_value,z=solve(q,True)
    if abs(global_value-1)>1e-6 and np.linalg.norm(q)>1e-6:
        raise RuntimeError((q,global_value))
    if local>best[0]+1e-8:
        best=(local,q)
        print("best",local,"q",q,"global",global_value,flush=True)
print("cycles",len(cycles),"patterns",len(patterns),"maximal",len(P),"polar vertices",len(verts),flush=True)
print("final",best,flush=True)
