"""Finite diagnostic for complementary two-size weights 5/12, 7/12."""
import json,time
from bipartite_mixed_path_search import score
import numpy as np

rng=np.random.default_rng(202610032)
best=1
start=time.time()
for it in range(3000):
    typ=it%3
    if typ==0:
        m=5
        core=[(i,i+1) for i in range(m-1)]
        edges=core+[(i,m+i) for i in range(m)]
        nv=2*m
    elif typ==1:
        m=6
        core=[(i,(i+1)%m) for i in range(m)]
        edges=core+[(i,m+i) for i in range(m)]
        nv=2*m
    else:
        m=3;nv=2*m
        edges=[(i,m+j) for i in range(m) for j in range(m) if rng.random()<.8]
        if len(edges)==0:continue
    weights=rng.choice([5,7],size=len(edges)).tolist()
    try:val,data=score(edges,weights,nv,tries=4)
    except Exception as ex:print('ERR',it,str(ex),flush=True);continue
    if val>best+1e-7:
        best=val
        item={'iteration':it,'ratio':val,'edges':edges,'weights':weights,'demand':data[0],'dual':data[1],'patterns':data[2]}
        print('BEST',json.dumps(item),flush=True)
        with open('tmp/weighted-proof/tight-bound-search-2026-10-03/bipartite_two_size_best.json','w') as f:json.dump(item,f,indent=2)
    if it%100==0:print('PROGRESS',it,'best',best,'seconds',round(time.time()-start,1),flush=True)
