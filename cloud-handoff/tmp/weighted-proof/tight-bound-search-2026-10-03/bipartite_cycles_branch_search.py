"""More finite diagnostics using the exact repeatable-pattern LP oracle."""
import json,time
from bipartite_mixed_path_search import score
import numpy as np

rng=np.random.default_rng(202610031)
sizes=[4,5,6,7,8,9,12]
best=4/3
start=time.time()
for it in range(2500):
    typ=it%3
    if typ in (0,1):
        m=4 if typ==0 else 6
        core=[(i,(i+1)%m) for i in range(m)]
    else:
        m=6
        core=[(i,(i-1)//2) for i in range(1,m)]
    edges=core+[(i,m+i) for i in range(m)]
    weights=rng.choice(sizes,size=len(edges)).tolist()
    try:val,data=score(edges,weights,2*m,tries=8)
    except Exception as ex:
        print('ERR',it,str(ex),flush=True);continue
    if val>best+1e-7:
        best=val
        item={'iteration':it,'ratio':val,'edges':edges,'weights':weights,'demand':data[0],'dual':data[1],'patterns':data[2]}
        print('BEST',json.dumps(item),flush=True)
        with open('tmp/weighted-proof/tight-bound-search-2026-10-03/bipartite_cycles_branch_best.json','w') as f:json.dump(item,f,indent=2)
    if it%100==0:print('PROGRESS',it,'best',best,'seconds',round(time.time()-start,1),flush=True)
