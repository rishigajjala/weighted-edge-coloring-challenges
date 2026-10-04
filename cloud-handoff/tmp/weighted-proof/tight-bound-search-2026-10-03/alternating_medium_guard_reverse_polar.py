"""Targeted stationary polar test with a medium reverse guard.

Core weights alternate A=.334 (rank2), B=.251 (rank3). At B->A
the medium guard .49 can coexist with either one A or two B, but
not with A+B. At A->B, heavy guard .749 fits one B and rejects A.
The .49 guard may appear twice in a color; all possibilities are kept.
"""
import collections
import itertools
import numpy as np
from scipy.optimize import linprog
from scipy.spatial import HalfspaceIntersection

W=(.334,.251); H=(.49,.749)
K=tuple(int(1/w+1e-9) for w in W)
G=tuple(int(1/h+1e-9) for h in H)
states=[]
for i in range(2):
    prev=(i-1)%2
    ss=[]
    for a,b,g in itertools.product(range(K[prev]+1),range(K[i]+1),range(G[i]+1)):
        if a*W[prev]+b*W[i]+g*H[i]<=1+1e-10: ss.append((a,b,g))
    states.append(ss)
offs=(0,len(states[0]),len(states[0])+len(states[1])); n=offs[-1]
Q=np.zeros((4,n)); mass=np.zeros((2,n)); mean=np.zeros((2,n)); hist=np.zeros((sum(k+1 for k in K),n))
arcs=collections.defaultdict(list)
for i in range(2):
    for j,(a,b,g) in enumerate(states[i]):
        pos=offs[i]+j; prev=(i-1)%2
        mass[i,pos]=1; Q[i,pos]=b;Q[2+i,pos]=g
        mean[i,pos]+=b;mean[prev,pos]-=a
        hist[sum(K[t]+1 for t in range(i))+b,pos]+=1
        hist[sum(K[t]+1 for t in range(prev))+a,pos]-=1
        arcs[(prev,a)].append(((i,b),pos))
Leq=np.vstack((mass,mean));Lrhs=np.r_[np.ones(2),np.zeros(2)]
Geq=np.vstack((mass,hist));Grhs=np.r_[np.ones(2),np.zeros(hist.shape[0])]
def solve(q,glob=False):
    a,b=(Geq,Grhs) if glob else (Leq,Lrhs)
    z=linprog(-(q@Q),A_eq=a,b_eq=b,bounds=(0,None),method="highs")
    if not z.success:raise RuntimeError(z.message)
    return -z.fun,z.x
cycles=set();nodes=list(arcs)
for start in nodes:
    def dfs(u,seen,path):
        for v,e in arcs[u]:
            if v==start and path:
                c=path+(e,)
                cycles.add(min(c[k:]+c[:k] for k in range(len(c))))
            elif v not in seen and len(path)<len(nodes):
                dfs(v,seen|{v},path+(e,))
    dfs(start,{start},())
P=np.unique(np.round(np.array([Q[:,list(c)].sum(axis=1)/(len(c)//2) for c in cycles]),12),axis=0)
keep=[]
for i,p in enumerate(P):
    if not any(np.all(q>=p-1e-10) and np.any(q>p+1e-10) for j,q in enumerate(P) if i!=j):keep.append(i)
Pmax=P[keep]
hs=np.vstack((np.c_[Pmax,-np.ones(len(Pmax))],np.c_[-np.eye(4),np.zeros(4)]))
q0=np.full(4,.1/max(1,np.max(Pmax.sum(axis=1))))
verts=np.unique(np.round(HalfspaceIntersection(hs,q0,qhull_options="QJ").intersections,10),axis=0)
best=(-1,None)
for q in verts:
    if np.min(q)<-1e-7 or np.max(Pmax@q)>1+1e-7:continue
    l,x=solve(q);g,z=solve(q,True)
    if l>best[0]+1e-8:
        best=(l,q)
        print("best",l,"q",q,"global",g,flush=True)
print("states",[len(s) for s in states],"cycles",len(cycles),"patterns",len(P),"maximal",len(Pmax),"polar",len(verts),flush=True)
print("final",best,flush=True)
