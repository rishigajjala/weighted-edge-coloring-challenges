"""Four-factor bipartite directed rank-reset/branch gadget.

Each hub has two copies each of high (.36) and low (.34) rank-two
spokes plus three B (.29) rank-three spokes. One of each fits (.99).
At each high/low A port a .68 guard rejects its spoke. Every B port
receives two .68 guards, either of which fits one B spoke. Low A guards
of each two-source shore feed the same B target; high A guards feed
the other B target. This creates Hall deficiency for low-only choices.

The fixed local point: one of each spoke per hub; each A spoke copy
has marginal 1/2; each B spoke copy marginal 1/3; each guard edge
marginal 1/2. Port-local laws use full A bursts or a guard, and at B
choose one incoming guard together with one B spoke. Optimize all
nonnegative edge-type profits against exact physical one-color states.
"""
import itertools
import numpy as np
from scipy.optimize import linprog

W=np.array([.36,.34,.29]); C=[2,2,3]
EDGES=[(0,1,2),(1,1,2),(0,0,3),(1,0,3),
       (2,1,0),(3,1,0),(2,0,1),(3,0,1)]
# Edge tuples: source factor, source spoke type 0=high 1=low, target B factor.
BITS=((np.arange(1<<8)[:,None]>>np.arange(8))&1).astype(np.uint8)
ok=np.ones(len(BITS),dtype=bool)
for target in range(4):
 ok&=BITS[:,[j for j,e in enumerate(EDGES) if e[2]==target]].sum(axis=1)<=1
ACTIVE=BITS[ok]
PAT={}
for mask in range(8):
 arr=[]
 for cnt in itertools.product(*(range(c+1) for c in C)):
  if cnt[0] and(mask&1):continue
  if cnt[1] and(mask&2):continue
  if (mask&4) and cnt[2]>1:continue
  if np.dot(W,cnt)<=1+1e-9:arr.append(cnt)
 PAT[mask]=np.array(arr,dtype=float)
MASKS=[]
for f in range(4):
 m=np.zeros(len(ACTIVE),dtype=np.uint8)
 for j,(source,typ,target) in enumerate(EDGES):
  if source==f:m+=ACTIVE[:,j]*(1<<typ)
  if target==f:m+=ACTIVE[:,j]*4
 MASKS.append(m)

local=np.r_[np.full(3,4.),np.full(8,.5)]
rows=[]
for step in range(300):
 ans=linprog(-local,A_ub=np.array(rows) if rows else None,
             b_ub=np.ones(len(rows)) if rows else None,
             bounds=[(0,1)]*11,method='highs')
 if not ans.success:raise RuntimeError(ans.message)
 q=ans.x[:3];b=ans.x[3:]
 total=ACTIVE@b;choices=[]
 for mask in MASKS:
  vals=[];cnts=[]
  for j in range(8):
   score=PAT[j]@q;k=np.argmax(score)
   vals.append(score[k]);cnts.append(PAT[j][k])
  total+=np.array(vals)[mask];choices.append(np.array(cnts)[mask])
 i=np.argmax(total)
 if total[i]<=1+1e-8:
  print('ratio',-ans.fun,'steps',step,'q',np.round(q,8).tolist(),
        'guards',np.round(b,8).tolist(),'best physical',total[i])
  break
 row=np.r_[sum(choices[f][i] for f in range(4)),ACTIVE[i]]
 if any(np.array_equal(row,x) for x in rows):raise RuntimeError('duplicate cut')
 rows.append(row)
else:raise RuntimeError('not converged')
