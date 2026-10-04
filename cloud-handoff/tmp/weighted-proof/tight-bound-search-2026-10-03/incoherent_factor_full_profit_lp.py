"""Optimize all three spoke profits and blocker profits on one mixed factor network.

Uses constraint generation: the pricing oracle enumerates every feasible
physical blocker matching and packs each hub exactly for candidate profits.
The local target is fixed at one spoke per bundle at every hub, and
full-burst port laws imply fixed blocker marginals. No theorem claim.
"""
import itertools
import numpy as np
from scipy.optimize import linprog

W=np.array([.42,.31,.26]); C=[2,3,3]
PATTERNS={}
for mask in range(8):
    v=[]
    for cnt in itertools.product(*(range(c+1) for c in C)):
        if any(cnt[i] and ((mask>>i)&1) for i in range(3)): continue
        if np.dot(W,cnt)<=1+1e-9: v.append(cnt)
    PATTERNS[mask]=np.array(v,dtype=float)

BITS=((np.arange(1<<12)[:,None]>>np.arange(12))&1).astype(np.uint8)

def topology(ap,bp):
    leftA=[0,3]; leftBC=[1,2,4,5]
    rightA=[0,3]; rightBC=[1,2,4,5]
    left=leftA+leftA+leftBC+leftBC
    right=rightA+[rightA[i] for i in ap]
    right+=rightBC+[rightBC[i] for i in bp]
    ok=np.ones(len(BITS),dtype=bool)
    for p in range(6):
        ok&=BITS[:,np.array(left)==p].sum(axis=1)<=1
        ok&=BITS[:,np.array(right)==p].sum(axis=1)<=1
    active=BITS[ok]
    masks=[]
    for endpoints in [left,right]:
        for fac in [0,1]:
            mask=sum(active[:,np.array(endpoints)==3*fac+port].sum(axis=1)*(1<<port)
                     for port in range(3))
            masks.append(mask)
    return active,masks

def run(ap,bp):
    active,masks=topology(ap,bp)
    local=np.r_[np.full(3,4.),np.full(4,.25),np.full(8,1/3)]
    rows=[]
    for step in range(250):
        ans=linprog(-local,A_ub=np.array(rows) if rows else None,
                    b_ub=np.ones(len(rows)) if rows else None,
                    bounds=[(0,1)]*15,method='highs')
        if not ans.success: raise RuntimeError(ans.message)
        q=ans.x[:3]; b=ans.x[3:]
        best_val=np.full(len(active),0.,dtype=float)
        best_cnt=[]
        for mask in masks:
            vals=[]; cnts=[]
            for j in range(8):
                scores=PATTERNS[j]@q
                k=np.argmax(scores)
                vals.append(scores[k]); cnts.append(PATTERNS[j][k])
            vals=np.array(vals); cnts=np.array(cnts)
            best_val+=vals[mask]
            best_cnt.append(cnts[mask])
        total=best_val+active@b
        i=np.argmax(total)
        if total[i]<=1+1e-8:
            return -ans.fun,step,ans.x,total[i]
        count=sum(cnt[i] for cnt in best_cnt)
        row=np.r_[count,active[i]]
        if not any(np.array_equal(row,x) for x in rows): rows.append(row)
        else: raise RuntimeError(('duplicate violating cut',total[i]))
    raise RuntimeError('no convergence')

best=(0.,None)
for ap in itertools.permutations(range(2)):
 for bp in itertools.permutations(range(4)):
    ratio,steps,x,p=run(ap,bp)
    if ratio>best[0]+1e-8:
        best=(ratio,(ap,bp))
        print('best',best,'steps',steps,'q',np.round(x[:3],6).tolist(),
              'b',np.round(x[3:],6).tolist(),flush=True)
