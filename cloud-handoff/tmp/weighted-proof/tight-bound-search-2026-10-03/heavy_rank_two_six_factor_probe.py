"""Fixed-count LP for rank-1/2/6 mixed bin with guard matching.

Hub has one edge .501, two .334, and six .144 per factor. Its
proposed local hub law chooses one of each with probability t and an
empty bin otherwise; each port law uses full bursts to explain the
spoke marginals and one unit blocker otherwise. The blocker marginal
at rank k is 1-t/k. Four bipartite factors, same-rank blocker matching.
All nonnegative spoke and blocker profits are optimized by pricing.
"""
import itertools
import numpy as np
from scipy.optimize import linprog

W=np.array([.501,.334,.144]);C=[1,2,6];R=3
PAT={}
for mask in range(1<<R):
 v=[]
 for cnt in itertools.product(*(range(c+1) for c in C)):
  if any(cnt[i] and ((mask>>i)&1) for i in range(R)):continue
  if np.dot(W,cnt)<=1+1e-9:v.append(cnt)
 PAT[mask]=np.array(v,dtype=float)
BITS=((np.arange(1<<6)[:,None]>>np.arange(6))&1).astype(np.uint8)

def run(swaps,t):
 left=[];right=[]
 for typ in range(R):
  left.extend([typ,R+typ]);right.extend(([typ,R+typ] if not swaps[typ] else [R+typ,typ]))
 masks=[]
 for ends in [left,right]:
  for fac in range(2):
   masks.append(sum(BITS[:,np.array(ends)==R*fac+typ].sum(axis=1)*(1<<typ)
                    for typ in range(R)))
 local=np.concatenate([np.full(R,4*t)]+[np.full(2,1-t/C[i]) for i in range(R)])
 rows=[]
 for step in range(200):
  ans=linprog(-local,A_ub=np.array(rows) if rows else None,
              b_ub=np.ones(len(rows)) if rows else None,
              bounds=[(0,1)]*9,method='highs')
  if not ans.success:raise RuntimeError(ans.message)
  q=ans.x[:R];b=ans.x[R:];total=BITS@b; choices=[]
  for mask in masks:
   vals=[];cnts=[]
   for j in range(1<<R):
    scores=PAT[j]@q;k=np.argmax(scores)
    vals.append(scores[k]);cnts.append(PAT[j][k])
   total+=np.array(vals)[mask];choices.append(np.array(cnts)[mask])
  i=np.argmax(total)
  if total[i]<=1+1e-8:return -ans.fun,step,ans.x
  row=np.r_[sum(choice[i] for choice in choices),BITS[i]]
  if any(np.array_equal(row,x) for x in rows):raise RuntimeError('duplicate cut')
  rows.append(row)
 raise RuntimeError('not converged')

best=(0.,None)
for t in np.linspace(.1,1,19):
 for swaps in itertools.product((0,1),repeat=R):
  ratio,steps,x=run(swaps,t)
  if ratio>best[0]+1e-8:
   best=(ratio,(t,swaps));print('best',best,'q',np.round(x[:R],6).tolist(),
                               'b',np.round(x[R:],6).tolist(),flush=True)
