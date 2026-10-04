"""Four-factor bipartite rank-2/3/4/5 count-law diagnostic.

Each factor has four spoke bundles of k_i=(2,3,4,5) copies and
weights (.334,.251,.201,.167), whose one-each mixed pattern fits.
At every port, one-each marginal is explained by a full k_i burst
versus a unit blocker, giving blocker p_i=1-1/k_i. Blockers form a
matching between corresponding port ranks on opposite-oriented
factors. Optimize every nonnegative spoke and blocker profit for this
fixed vertex-local target by exact physical-color pricing LP.
"""
import itertools
import numpy as np
from scipy.optimize import linprog

W=np.array([.334,.251,.201,.167]); C=[2,3,4,5]; R=4
PATTERNS={}
for mask in range(1<<R):
    patterns=[]
    for cnt in itertools.product(*(range(c+1) for c in C)):
        if any(cnt[i] and ((mask>>i)&1) for i in range(R)): continue
        if np.dot(W,cnt)<=1+1e-9: patterns.append(cnt)
    PATTERNS[mask]=np.array(patterns,dtype=float)

BITS=((np.arange(1<<8)[:,None]>>np.arange(8))&1).astype(np.uint8)

def price_setup(swaps):
    # Each rank has two blockers, joining left factors 0/2 to right 1/3.
    left=[];right=[]
    for typ in range(R):
        left.extend([typ,R+typ])
        right.extend(([typ,R+typ] if not swaps[typ] else [R+typ,typ]))
    local=np.concatenate([np.full(R,4.)]+[np.full(2,1-1/C[i]) for i in range(R)])
    spoke_mask=[]
    for ends in [left,right]:
        for fac in range(2):
            m=sum(BITS[:,np.array(ends)==R*fac+typ].sum(axis=1)*(1<<typ)
                  for typ in range(R))
            spoke_mask.append(m)
    return local,spoke_mask

def run(swaps):
    local,masks=price_setup(swaps)
    rows=[]
    for step in range(300):
        ans=linprog(-local,A_ub=np.array(rows) if rows else None,
                    b_ub=np.ones(len(rows)) if rows else None,
                    bounds=[(0,1)]*12,method='highs')
        if not ans.success:raise RuntimeError(ans.message)
        q=ans.x[:R];b=ans.x[R:]
        total=BITS@b
        choices=[]
        for mask in masks:
            vals=[];cnts=[]
            for j in range(1<<R):
                scores=PATTERNS[j]@q;k=np.argmax(scores)
                vals.append(scores[k]);cnts.append(PATTERNS[j][k])
            total+=np.array(vals)[mask]
            choices.append(np.array(cnts)[mask])
        i=np.argmax(total)
        if total[i]<=1+1e-8:return -ans.fun,step,ans.x,total[i]
        row=np.r_[sum(choice[i] for choice in choices),BITS[i]]
        if any(np.array_equal(row,x) for x in rows):
            raise RuntimeError(('duplicate cut',total[i]))
        rows.append(row)
    raise RuntimeError('not converged')

best=(0.,None)
for swaps in itertools.product((0,1),repeat=R):
    ratio,steps,x,price=run(swaps)
    if ratio>best[0]+1e-8:
        best=(ratio,swaps)
        print('best',best,'steps',steps,'q',np.round(x[:R],6).tolist(),
              'b',np.round(x[R:],6).tolist(),flush=True)
