"""Targeted two-core-vertex multirank opposing-guard polar diagnostic.

Core physical weights .334,.251,.08 on the same u-v bundle; private heavy
guards .666 at u and .749 at v. This probes incompatible preferred core-bin
partitions on the two sides with a 2+1+1 mixed core bin. Fixed-support
repeatable-count LP only; floating vertices are diagnostic until rationalized.
"""
import itertools
import numpy as np
from scipy.optimize import linprog
from scipy.spatial import HalfspaceIntersection

W=(.334,.251,.08)
H=(.666,.749)
R=(2,3,12)
P=[];U=[];V=[]
for x in itertools.product(*(range(t+1) for t in R)):
    load=sum(a*w for a,w in zip(x,W))
    if load>1+1e-10:continue
    for hu in (0,1):
        if load+hu*H[0]<=1+1e-10:U.append(x+(hu,))
        for hv in (0,1):
            if load+hv*H[1]<=1+1e-10:V.append(x+(hv,))
            if load+hu*H[0]<=1+1e-10 and load+hv*H[1]<=1+1e-10:
                P.append(x+(hu,hv))
P=np.unique(np.asarray(P,float),axis=0)
U=np.unique(np.asarray(U,float),axis=0)
V=np.unique(np.asarray(V,float),axis=0)
print('patterns',len(P),len(U),len(V),flush=True)

# Local distributions on U and V with equal three core means.
nu,nv=len(U),len(V)
EQ=np.zeros((5,nu+nv)); RHS=np.zeros(5)
EQ[0,:nu]=1;EQ[1,nu:]=1;RHS[:2]=1
for j in range(3):EQ[2+j,:nu]=U[:,j];EQ[2+j,nu:]=-V[:,j]

def local_value(q):
    # Count each core profit only on U; V contributes its private guard only.
    reward=np.r_[U[:,:3]@q[:3]+U[:,3]*q[3],V[:,3]*q[4]]
    ans=linprog(-reward,A_eq=EQ,b_eq=RHS,bounds=(0,None),method='highs')
    if not ans.success:raise RuntimeError(ans.message)
    return -ans.fun,ans.x

half=np.vstack([np.c_[P,-np.ones(len(P))],np.c_[-np.eye(5),np.zeros(5)]])
q0=np.full(5,1/(max(P.sum(axis=1))+2))
hs=HalfspaceIntersection(half,q0)
Q=np.unique(np.round(hs.intersections,10),axis=0)
print('polar vertices',len(Q),flush=True)
best=(0,None)
for i,q in enumerate(Q):
    val,lam=local_value(q)
    if val>best[0]+1e-8:
        x=(lam[:nu]@U[:,:3]).tolist()+[(lam[:nu]@U[:,3]),(lam[nu:]@V[:,3])]
        best=(val,{'q':q.tolist(),'x':x,'vertex_index':i})
        print('best',best,flush=True)
print('FINAL',best,flush=True)
