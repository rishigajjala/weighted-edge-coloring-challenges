"""Classify open threshold cells for a two-core rank-2->rank-3 path.

Path weights a in (1/3,1/2), b in (1/4,1/3), a>b; guards
1-a,1-b and unit terminal. Each threshold cell has the same finite
physical count patterns, hence the same local/global configuration
polytopes and all-profit gap. A dense rational-offset lattice finds
candidate open cells; full polar gauge is then optimized per cell.
This is a numerical finite-cell diagnostic, not a formal cell proof.
"""
import itertools
import sys
import numpy as np
from scipy.optimize import linprog
from scipy.spatial import HalfspaceIntersection

K=int(sys.argv[1]) if len(sys.argv)>1 else 3
CAND=list(itertools.product(range(3),range(K+1),range(2),range(2),range(2)))
LCAND=[list(itertools.product(range(3),range(2))),
       list(itertools.product(range(3),range(K+1),range(2))),
       list(itertools.product(range(K+1),range(2)))]

def patterns(a,b):
 hs=[1-a,1-b,1.]
 g=tuple(c for c in CAND if a*c[0]+hs[0]*c[2]<=1+1e-10
         and a*c[0]+b*c[1]+hs[1]*c[3]<=1+1e-10
         and b*c[1]+hs[2]*c[4]<=1+1e-10)
 local=[tuple(c for c in LCAND[0] if a*c[0]+hs[0]*c[1]<=1+1e-10),
        tuple(c for c in LCAND[1] if a*c[0]+b*c[1]+hs[1]*c[2]<=1+1e-10),
        tuple(c for c in LCAND[2] if b*c[0]+hs[2]*c[1]<=1+1e-10)]
 return g,tuple(local)

def gauge(g,local):
 A=np.array(g,dtype=float).T;dim=5
 hs=np.vstack([np.column_stack([A.T,-np.ones(A.shape[1])]),
               np.column_stack([-np.eye(dim),np.zeros(dim)])])
 inner=np.full(dim,1/(2*max(A.sum(axis=0))+2))
 polar=HalfspaceIntersection(hs,inner,qhull_options='Qx').intersections
 polar=np.unique(np.round(polar,10),axis=0)
 P=[np.array(x,dtype=float).T for x in local]
 offset=np.cumsum([0]+[p.shape[1] for p in P]);n=offset[-1]
 eq=[];rhs=[]
 for v,p in enumerate(P):
  row=np.zeros(n);row[offset[v]:offset[v+1]]=1;eq.append(row);rhs.append(1)
 for t in range(2):
  row=np.zeros(n);row[offset[t]:offset[t+1]]=P[t][t]
  row[offset[t+1]:offset[t+2]]=-P[t+1][0]
  eq.append(row);rhs.append(0)
 eq=np.array(eq);rhs=np.array(rhs)
 best=(0,None)
 for q in polar:
  obj=np.r_[q[0]*P[0][0]+q[2]*P[0][1],
            q[0]*P[1][0]+q[1]*P[1][1]+q[3]*P[1][2],
            q[1]*P[2][0]+q[4]*P[2][1]]
  # Core types 0 and 1 are double-counted in obj; choose one endpoint.
  obj[offset[1]:offset[2]]-=q[0]*P[1][0]
  obj[offset[2]:offset[3]]-=q[1]*P[2][0]
  ans=linprog(-obj,A_eq=eq,b_eq=rhs,bounds=[(0,None)]*n,method='highs')
  if not ans.success:raise RuntimeError(ans.message)
  if -ans.fun>best[0]+1e-8:best=(-ans.fun,q)
 return best,len(polar)

cells={}
for p in range(201,300):
 for q in range(int(600/(K+1))+1,int(600/K)):
  a=(p+.271828)/600;b=(q+.314159)/600
  sig=patterns(a,b)
  if sig not in cells:cells[sig]=(a,b)
print('open-cell signatures',len(cells),flush=True)
best=(0,None)
for i,(sig,(a,b)) in enumerate(cells.items()):
 val,nv=gauge(*sig)
 print('cell',i,'a,b',round(a,6),round(b,6),'a+2b',round(a+2*b,6),
       '2a+b',round(2*a+b,6),'gauge',val[0],
       'q',np.round(val[1],8).tolist(),'polar',nv,flush=True)
 if val[0]>best[0]+1e-8:
  best=(val[0],(a,b,val[1],len(sig[0]),nv))
  print('best',best,'cell',i,flush=True)
print('FINAL',best,flush=True)
