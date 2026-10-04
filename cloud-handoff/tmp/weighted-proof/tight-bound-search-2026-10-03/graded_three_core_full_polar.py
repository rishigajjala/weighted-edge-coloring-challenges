"""Attempt exact all-profit gauge for one 2->3->4 graded path template.

Enumerate the polar of the global one-color count hull, then optimize
the locally consistent means at each polar vertex. Numerical polyhedral
diagnostic only; rational certification would be needed for a theorem.
"""
import runpy
from pathlib import Path
import numpy as np
from scipy.optimize import linprog
from scipy.spatial import HalfspaceIntersection

x=runpy.run_path(str(Path(__file__).with_name('graded_rank_transition_path_lp.py')))
A=x['A']
LOCAL=x['LOCAL']
dim=A.shape[0]
H=np.vstack([np.column_stack([A.T,-np.ones(A.shape[1])]),
             np.column_stack([-np.eye(dim),np.zeros(dim)])])
interior=np.full(dim,1/(2*max(A.sum(axis=0))+2))
print('polar facets',len(H),'interior max',max(H[:,:-1]@interior+H[:,-1]),flush=True)
polar=HalfspaceIntersection(H,interior,qhull_options='Qx').intersections
polar=np.unique(np.round(polar,10),axis=0)
print('polar vertices',len(polar),flush=True)

# z variables are each local vertex's pattern probabilities.
offset=[];n=0
for types,P in LOCAL:
 offset.append(n);n+=P.shape[1]
Aeq=[];beq=[]
for v,(types,P) in enumerate(LOCAL):
 row=np.zeros(n);row[offset[v]:offset[v]+P.shape[1]]=1
 Aeq.append(row);beq.append(1)
for t in range(3):
 row=np.zeros(n)
 for v,sgn in [(t,1),(t+1,-1)]:
  types,P=LOCAL[v]
  j=[j for j,(typ,w) in enumerate(types) if typ==t][0]
  row[offset[v]:offset[v]+P.shape[1]]=sgn*P[j]
 Aeq.append(row);beq.append(0)
Aeq=np.array(Aeq);beq=np.array(beq)

best=(0,None,None,None)
for i,q in enumerate(polar):
 objective=np.zeros(n)
 for t in range(dim):
  v=t if t<3 else t-3
  types,P=LOCAL[v]
  j=[j for j,(typ,w) in enumerate(types) if typ==t][0]
  objective[offset[v]:offset[v]+P.shape[1]]+=q[t]*P[j]
 ans=linprog(-objective,A_eq=Aeq,b_eq=beq,bounds=[(0,None)]*n,method='highs')
 if not ans.success:raise RuntimeError(ans.message)
 ratio=-ans.fun
 if ratio>best[0]+1e-8:
  best=(ratio,i,q,ans.x)
  print('best',ratio,'q',np.round(q,6).tolist(),flush=True)
print('FINAL',best[0],flush=True)
if best[3] is not None:
 means=np.zeros(dim)
 for t in range(dim):
  v=t if t<3 else t-3
  types,P=LOCAL[v]
  j=[j for j,(typ,w) in enumerate(types) if typ==t][0]
  means[t]=P[j]@best[3][offset[v]:offset[v]+P.shape[1]]
 print('FINAL q',np.round(best[2],10).tolist(),'local mean',np.round(means,10).tolist(),flush=True)
 for v,(types,P) in enumerate(LOCAL):
  z=best[3][offset[v]:offset[v]+P.shape[1]]
  print('vertex',v,[(round(float(z[j]),10),P[:,j].tolist()) for j in range(len(z)) if z[j]>1e-8],flush=True)
