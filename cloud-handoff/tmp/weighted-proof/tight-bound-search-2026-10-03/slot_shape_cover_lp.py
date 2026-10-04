"""Explore fixed slot-shape palettes. Finite-grid LP is diagnostic only.

A mode is a bin partition. An edge may be put at any slot at least its weight.
Nested Hall count bounds guarantee a bipartite proper edge coloring of the
slot copies. Choose weight-dependent fractions across all modes and charge
each mode enough for the worst input-bin pattern at every Hall threshold.
"""
import sys,json
from pathlib import Path
import numpy as np
from scipy.optimize import linprog
from scipy.sparse import coo_matrix

W=int(sys.argv[1]) if len(sys.argv)>1 else 12
def partitions(n,maxpart=None):
    if n==0:
        yield []
    else:
        for k in range(min(n,maxpart or n),1-1,-1):
            for tail in partitions(n-k,k):yield [k]+tail
parts=list(partitions(W))
bins=np.array([[p.count(i) for i in range(1,W+1)] for p in parts],dtype=int)
alloc={};qidx=len(parts);nv=len(parts)+1
for m,p in enumerate(parts):
    for i in range(1,max(p)+1):alloc[m,i]=nv;nv+=1
rr=[];cc=[];vv=[];rhs=[]
for m,p in enumerate(parts):
    thresholds=[1]+[s+1 for s in sorted(set(p)) if s<max(p)]
    for t in thresholds:
        cap=sum(s>=t for s in p)
        for B in bins:
            row=len(rhs);rhs.append(0.)
            rr.append(row);cc.append(m);vv.append(-cap)
            for i in range(t,max(p)+1):
                if B[i-1]:rr.append(row);cc.append(alloc[m,i]);vv.append(int(B[i-1]))
charge=np.array([1/(W//i) for i in range(1,W+1)])
for B in bins:
    row=len(rhs);rhs.append(-float(B@charge));rr.append(row);cc.append(qidx);vv.append(-1.)
    for (m,i),v in alloc.items():
        if B[i-1]:rr.append(row);cc.append(v);vv.append(-float(B[i-1]*charge[i-1]))
for i in range(1,W+1):
    row=len(rhs);rhs.append(1.)
    for (m,j),v in alloc.items():
        if i==j:rr.append(row);cc.append(v);vv.append(1.)
A=coo_matrix((vv,(rr,cc)),shape=(len(rhs),nv)).tocsr()
c=np.r_[np.ones(len(parts)+1),np.zeros(nv-len(parts)-1)]
print(json.dumps(dict(W=W,modes=len(parts),variables=nv,rows=len(rhs),nonzero=A.nnz)),flush=True)
r=linprog(c,A_ub=A,b_ub=rhs,bounds=(0,None),method='highs')
print(r.message,flush=True)
if r.success:
    result=dict(W=W,cost=float(r.fun),remainder=float(r.x[qidx]),modes=[])
    for m,p in enumerate(parts):
        if r.x[m]>1e-8:
            result['modes'].append(dict(slots=p,cost=float(r.x[m]),fractions={str(i):float(r.x[alloc[m,i]]) for i in range(1,max(p)+1) if r.x[alloc[m,i]]>1e-8}))
    print(json.dumps(result),flush=True)
    Path(__file__).with_name(f'slot_shape_cover_W{W}.json').write_text(json.dumps(result,indent=2))
