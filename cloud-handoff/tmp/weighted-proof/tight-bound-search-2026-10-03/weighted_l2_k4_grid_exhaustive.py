"""Exhaust 8^6 weighted incidence matrices on K4, all signings.

Each edge has first endpoint coefficient 1/2 or 1 and second endpoint
coefficient in {+/-1/2,+/-1}. Column-wide sign is normalized at first
endpoint. All arithmetic is exact integer after multiplication by 2.
"""
import json
import itertools
import numpy as np

edges=list(itertools.combinations(range(4),2))
m=len(edges)
bits=((np.arange(1<<(m-1))[:,None]>>np.arange(m-1))&1)
signs=np.column_stack((np.ones(len(bits),dtype=np.int16),2*bits-1))
total=8**m
batch=512
for base in range(0,total,batch):
    size=min(batch,total-base)
    idx=np.arange(base,base+size,dtype=np.int64)
    aa=np.zeros((size,4,m),dtype=np.int16)
    for e,(u,v) in enumerate(edges):
        digit=idx%8
        idx//=8
        aa[:,u,e]=1+digit//4
        aa[:,v,e]=np.array([-2,-1,1,2],dtype=np.int16)[digit%4]
    sums=np.einsum('bve,se->bsv',aa,signs,optimize=True)
    sq=np.sum(sums.astype(np.int32)**2,axis=2)
    mins=np.min(sq,axis=1)
    bad=(sq==mins[:,None])&(np.max(np.abs(sums),axis=2)>4)
    if np.any(bad):
        bi,si=np.argwhere(bad)[0]
        print(json.dumps({"index":int(base+bi),"matrix_twice":aa[bi].tolist(),
                          "sign":signs[si].tolist(),"sum_twice":sums[bi,si].tolist(),
                          "minimum_sq":int(mins[bi])}),flush=True)
        break
else:
    print("NO_COUNTEREXAMPLE",total,flush=True)
