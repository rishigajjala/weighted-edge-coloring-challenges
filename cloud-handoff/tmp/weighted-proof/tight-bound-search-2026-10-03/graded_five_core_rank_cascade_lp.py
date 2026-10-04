"""Targeted asymptotic LP on a five-core graded path crossing 2,3,4,5.

Enumerates exact physical one-color count patterns, computes local and
global covering LPs for structured nonuniform multiplicities. A finite
diagnostic only. Guard weights are outgoing complements; terminal unit.
"""
import itertools
import numpy as np
from scipy.optimize import linprog

W=np.array([.49,.42,.331,.249,.199]);m=len(W)
H=np.r_[1-W,1.]
CAP=[int(1/w+1e-9) for w in W]
ST=[]
for x in itertools.product(*(range(k+1) for k in CAP)):
 for y in itertools.product((0,1),repeat=m+1):
  if H[0]*y[0]+W[0]*x[0]>1+1e-9:continue
  if any(H[i]*y[i]+W[i-1]*x[i-1]+W[i]*x[i]>1+1e-9 for i in range(1,m)):continue
  if H[m]*y[m]+W[m-1]*x[m-1]>1+1e-9:continue
  ST.append(tuple(x)+tuple(y))
A=np.array(ST,dtype=float).T
print('global states',len(ST),flush=True)
LOCAL=[]
for v in range(m+1):
 if v==0: types=[(0,W[0]),(m,H[0])]
 elif v==m: types=[(m-1,W[m-1]),(2*m,H[m])]
 else: types=[(v-1,W[v-1]),(v,W[v]),(m+v,H[v])]
 pats=[]
 for cnt in itertools.product(*(range(CAP[t]+1) if t<m else (0,1) for t,w in types)):
  if sum(cnt[j]*types[j][1] for j in range(len(types)))<=1+1e-9:pats.append(cnt)
 LOCAL.append((types,np.array(pats,dtype=float).T))

def cover(P,d):
 ans=linprog(np.ones(P.shape[1]),A_ub=-P,b_ub=-np.array(d,dtype=float),
             bounds=[(0,None)]*P.shape[1],method='highs')
 if not ans.success:raise RuntimeError(ans.message)
 return ans.fun

CORES=[(2,2,2,2,2),(4,4,4,4,4),(4,4,3,2,1),(4,3,3,2,2),
       (2,2,3,4,5),(4,2,4,2,4),(2,4,2,4,2),(4,4,2,2,2),
       (2,2,2,4,4),(3,3,4,4,4),(5,4,3,2,1),(2,3,4,5,5)]
best=(0.,None)
for core in CORES:
 choices=[]
 for v in range(m+1):
  if v==0: choices.append(sorted(set([0,core[0]])))
  elif v==m: choices.append(sorted(set([0,core[-1]])))
  else:choices.append(sorted(set([0,core[v-1],core[v]])))
 for guards in itertools.product(*choices):
  d=np.r_[core,guards]
  bp=max(cover(P,[d[t] for t,w in types]) for types,P in LOCAL)
  global_cost=cover(A,d)
  ratio=global_cost/bp
  if ratio>best[0]+1e-7:
   best=(ratio,(core,guards,bp,global_cost))
   print('best',best,flush=True)
