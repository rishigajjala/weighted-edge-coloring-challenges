"""Small bipartite mixed-hull falsification; no finite scan proves a bound.

Enumerates all heavy matchings, but treats fluid recourse exactly with a compact
perspective-flow LP. Alternates its nonnegative support prices and the local LP
to find high-gap local vertices. Heavy support is unrestricted.
"""
import sys,json,time
from pathlib import Path
import numpy as np
from scipy.optimize import linprog
from scipy.sparse import coo_matrix

n=int(sys.argv[1]) if len(sys.argv)>1 else 3
trials=int(sys.argv[2]) if len(sys.argv)>2 else 100
rng=np.random.default_rng(11959+n)
edges=[(i,n+j) for i in range(n) for j in range(n)]
E=len(edges); V=2*n
inc=np.zeros((V,E))
for j,(u,v) in enumerate(edges):inc[u,j]=inc[v,j]=1
matchings=[]
def rec(i,used,bits):
    if i==n:
        matchings.append(bits.copy());return
    rec(i+1,used,bits)
    for j in range(n):
        if not(used>>j&1):
            bits[i*n+j]=1;rec(i+1,used|1<<j,bits);bits[i*n+j]=0
rec(0,0,np.zeros(E))
M=np.array(matchings); nm=len(M);nv=nm*(1+E)
cost=np.r_[np.ones(nm),np.zeros(nm*E)]

def make(w):
    rr=[];cc=[];vv=[]
    # Demand rows, then one vertex capacity row per heavy matching.
    for m,b in enumerate(M):
        for e in np.flatnonzero(b):rr.append(e);cc.append(m);vv.append(-1.)
        residual=1-inc@(w*b)
        for v in range(V):
            row=2*E+m*V+v
            if residual[v]>1e-12:rr.append(row);cc.append(m);vv.append(-residual[v])
        for e,(u,v) in enumerate(edges):
            col=nm+m*E+e
            rr.append(E+e);cc.append(col);vv.append(-1.)
            for z in [u,v]:rr.append(2*E+m*V+z);cc.append(col);vv.append(1.)
    A=coo_matrix((vv,(rr,cc)),shape=(2*E+nm*V,nv)).tocsr()
    Aloc=np.block([[inc,np.zeros_like(inc)],[inc*w,inc]])
    return A,Aloc

def gauge(pt,A):
    r=linprog(cost,A_ub=A,b_ub=np.r_[-pt,np.zeros(nm*V)],bounds=(0,None),method='highs')
    if not r.success:raise RuntimeError(r.message)
    return float(r.fun),-r.ineqlin.marginals[:2*E]

best=0.;records=[];started=time.time()
for trial in range(trials):
    if trial<trials//2:w=rng.choice([.5,1.],size=E)
    else:w=rng.choice([.5,2/3,.75,1.],size=E)
    A,Aloc=make(w)
    for start in range(12 if n==3 else 5):
        q=np.exp(rng.uniform(-2,2,size=2*E))
        prev=0
        for it in range(12):
            r=linprog(-q,A_ub=Aloc,b_ub=np.ones(2*V),bounds=(0,None),method='highs')
            pt=r.x
            val,qd=gauge(pt,A)
            if val>best+1e-8:
                best=val
                out=dict(n=n,trial=trial,start=start,iteration=it,ratio=val,
                  weights=w.tolist(),local=pt.tolist(),prices=qd.tolist(),elapsed=time.time()-started)
                records.append(out);print(json.dumps(out),flush=True)
                Path(__file__).with_name(f'arbitrary_heavy_fluid_n{n}.json').write_text(json.dumps(records,indent=2))
            if val<=prev+1e-9:break
            prev=val;q=qd+1e-10*q
print('FINISHED; numerical evidence only',best,'elapsed',time.time()-started,flush=True)
