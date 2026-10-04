"""Exact finite weighted coloring of two opposite K_{D-r,D} heavy blocks.

Low U/V vertices are linked by the crown graph K_{D,D} minus a perfect
matching of rank-two (.4) core edges. Heavy unit edges form two disjoint
K_{D-r,D} blocks in opposite orientations. Local bp is D. The MILP uses
2*heavy-degree + core-degree <=2 in each color at each vertex, exact for
unit heavy and .4 core. This tests a shared-heavy/free-set expansion gadget.
"""
import sys
import numpy as np
from scipy.optimize import milp,Bounds,LinearConstraint
from scipy.sparse import lil_matrix

D=int(sys.argv[1]) if len(sys.argv)>1 else 5
r=int(sys.argv[2]) if len(sys.argv)>2 else 2
M=int(sys.argv[3]) if len(sys.argv)>3 else 6
blocks=[int(z) for z in sys.argv[4].split(',')] if len(sys.argv)>4 else None
assert 0<r<D
if blocks is not None:assert sum(blocks)==D and min(blocks)>=2

# shore labels: U high 0..D-r-1, U low D-r..2D-r-1;
# V high 0..D-r-1, V low D-r..2D-r-1.
nh=D-r;n=nh+D
edges=[]
for u in range(nh):
 for j in range(D):edges.append((u,nh+j,2))
for i in range(D):
 for v in range(nh):edges.append((nh+i,v,2))
excluded={(i,i) for i in range(D)}
if blocks is not None:
 off=0
 for size in blocks:
  for i in range(size):excluded.add((off+i,off+(i+1)%size))
  off+=size
for i in range(D):
 for j in range(D):
  if (i,j) not in excluded:edges.append((nh+i,nh+j,1))
E=len(edges);N=E*M
A=lil_matrix((E+2*n*M,N),dtype=float)
lower=np.r_[np.ones(E),np.full(2*n*M,-np.inf)]
upper=np.r_[np.ones(E),np.full(2*n*M,2.)]
for e,(u,v,w) in enumerate(edges):
 for c in range(M):
  col=e*M+c
  A[e,col]=1
  A[E+u*M+c,col]=w
  A[E+n*M+v*M+c,col]=w
res=milp(np.zeros(N),integrality=np.ones(N),bounds=Bounds(np.zeros(N),np.ones(N)),
         constraints=LinearConstraint(A.tocsr(),lower,upper),
         options={'time_limit':120,'mip_rel_gap':0.0})
print('D,r,M,blocks,edges,status,message',D,r,M,blocks,E,res.status,res.message,flush=True)
if res.x is not None:
 sol=np.rint(res.x).astype(int).reshape(E,M)
 print('assigned',int(sol.sum()),'max violation',float(np.max(A@res.x-upper)),flush=True)
 for c in range(M):
  h=sum(sol[e,c] for e,x in enumerate(edges) if x[2]==2)
  s=sum(sol[e,c] for e,x in enumerate(edges) if x[2]==1)
  print('color',c,'heavy',h,'core',s,flush=True)
