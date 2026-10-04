"""Targeted asymptotic LP diagnostic for nonuniform graded-path demands.

Three core bundles with strictly decreasing weights across ranks 2,3,4;
complementary heavy guards at each path vertex. All repeated physical
edge types are represented by integer count patterns per color. Local
and global covering LP optima are the asymptotic scaled multiplicity
costs. Search selected nonuniform demand profiles, not a theorem.
"""
import itertools
import numpy as np
from scipy.optimize import linprog

W=np.array([.49,.33,.249]); H=np.array([1-W[0],1-W[1],1-W[2],1.])
CAP=[int(1/w+1e-9) for w in W]
STATES=[]
for x in itertools.product(*(range(k+1) for k in CAP)):
 for y in itertools.product((0,1),repeat=4):
  if H[0]*y[0]+W[0]*x[0]>1+1e-9:continue
  if any(H[i]*y[i]+W[i-1]*x[i-1]+W[i]*x[i]>1+1e-9 for i in (1,2)):continue
  if H[3]*y[3]+W[2]*x[2]>1+1e-9:continue
  STATES.append(tuple(x)+tuple(y))
A=np.array(STATES,dtype=float).T
print('global states',len(STATES),flush=True)
LOCAL=[]
for v in range(4):
 if v==0: types=[(0,W[0]),(3,H[0])]
 elif v==3: types=[(2,W[2]),(6,H[3])]
 else: types=[(v-1,W[v-1]),(v,W[v]),(3+v,H[v])]
 pats=[]
 for cnt in itertools.product(*(range(CAP[t] +1) if t<3 else (0,1) for t,w in types)):
  if sum(cnt[j]*types[j][1] for j in range(len(types)))<=1+1e-9:
   pats.append(cnt)
 LOCAL.append((types,np.array(pats,dtype=float).T))

def solve_cover(P,d):
 ans=linprog(np.ones(P.shape[1]),A_ub=-P,b_ub=-np.array(d,dtype=float),
             bounds=[(0,None)]*P.shape[1],method='highs')
 if not ans.success:raise RuntimeError(ans.message)
 return ans.fun

best=(0.,None)
for core in [(2,2,2),(2,3,3),(2,3,4),(3,2,4),(4,3,2),(4,4,4),
             (3,3,4),(2,4,4),(4,2,2),(2,2,4)]:
 for guards in itertools.product(range(5),repeat=4):
  demand=np.r_[core,guards]
  if not demand.any():continue
  bp=max(solve_cover(P,[demand[t] for t,w in types]) for types,P in LOCAL)
  if bp<=0:continue
  glob=solve_cover(A,demand)
  ratio=glob/bp
  if ratio>best[0]+1e-7:
   best=(ratio,(core,guards,bp,glob))
   print('best',best,flush=True)
