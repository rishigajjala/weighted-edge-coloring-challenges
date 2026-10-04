"""All-nonnegative-profit polar gauge for .34 -> .30 graded two-core path.

Exact physical count patterns and locally feasible mean polytope;
Qhull and LP use floating-point arithmetic. Checks whether this
small rank-transition support alone can exceed 4/3.
"""
import itertools
import numpy as np
from scipy.optimize import linprog
from scipy.spatial import HalfspaceIntersection

W=[.34,.30];H=[.66,.70,1.]
G=[]
for x0,x1,y0,y1,y2 in itertools.product(range(3),range(4),range(2),range(2),range(2)):
 if W[0]*x0+H[0]*y0>1+1e-9:continue
 if W[0]*x0+W[1]*x1+H[1]*y1>1+1e-9:continue
 if W[1]*x1+H[2]*y2>1+1e-9:continue
 G.append((x0,x1,y0,y1,y2))
A=np.array(G,dtype=float).T
LOCAL=[]
for types in [[(0,W[0]),(2,H[0])],[(0,W[0]),(1,W[1]),(3,H[1])],
              [(1,W[1]),(4,H[2])]]:
 pats=[]
 for cnt in itertools.product(*(range(3) if t==0 else (range(4) if t==1 else range(2)) for t,w in types)):
  if sum(cnt[j]*types[j][1] for j in range(len(types)))<=1+1e-9:pats.append(cnt)
 LOCAL.append((types,np.array(pats,dtype=float).T))

dim=5
HSP=np.vstack([np.column_stack([A.T,-np.ones(A.shape[1])]),
               np.column_stack([-np.eye(dim),np.zeros(dim)])])
inner=np.full(dim,1/(2*max(A.sum(axis=0))+2))
verts=HalfspaceIntersection(HSP,inner,qhull_options='Qx').intersections
verts=np.unique(np.round(verts,10),axis=0)
print('global patterns',A.shape[1],'polar vertices',len(verts),flush=True)

offset=[];n=0
for types,P in LOCAL:offset.append(n);n+=P.shape[1]
eq=[];rhs=[]
for v,(types,P) in enumerate(LOCAL):
 row=np.zeros(n);row[offset[v]:offset[v]+P.shape[1]]=1
 eq.append(row);rhs.append(1)
for t in (0,1):
 row=np.zeros(n)
 for v,sgn in [(t,1),(t+1,-1)]:
  types,P=LOCAL[v];j=[j for j,(typ,w) in enumerate(types) if typ==t][0]
  row[offset[v]:offset[v]+P.shape[1]]=sgn*P[j]
 eq.append(row);rhs.append(0)
eq=np.array(eq);rhs=np.array(rhs)

best=(0,None,None)
for q in verts:
 obj=np.zeros(n)
 for t in range(dim):
  v=t if t<2 else t-2
  types,P=LOCAL[v];j=[j for j,(typ,w) in enumerate(types) if typ==t][0]
  obj[offset[v]:offset[v]+P.shape[1]]+=q[t]*P[j]
 ans=linprog(-obj,A_eq=eq,b_eq=rhs,bounds=[(0,None)]*n,method='highs')
 if not ans.success:raise RuntimeError(ans.message)
 if -ans.fun>best[0]+1e-8:
  best=(-ans.fun,q,ans.x)
  print('best',best[0],'q',np.round(q,8).tolist(),flush=True)
print('FINAL',best[0],flush=True)
