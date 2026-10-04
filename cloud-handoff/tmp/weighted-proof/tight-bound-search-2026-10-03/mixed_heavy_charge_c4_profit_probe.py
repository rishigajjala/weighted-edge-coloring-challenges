"""Targeted alternating C4 with composite vs strict heavy guards.

Core edge weights A=.251, B=.201 alternate around the bipartite C4.
Lax heavy .54 fits A+B (charge 1+1/3+1/4>4/3); strict .749 fits
A alone but not A+B. Optimizes 4-vertex local configuration laws against
physical one-color global patterns in sampled nonnegative profit directions.
"""
import itertools
import numpy as np
from scipy.optimize import linprog

END=((0,1),(1,2),(2,3),(3,0))
W=(.251,.201,.251,.201)
H=(.54,.749,.54,.749)
K=(3,4,3,4)
G=[]
for core in itertools.product(*(range(k+1) for k in K)):
  for guard in itertools.product((0,1),repeat=4):
    load=[H[v]*guard[v] for v in range(4)]
    for e,(u,v) in enumerate(END):load[u]+=W[e]*core[e];load[v]+=W[e]*core[e]
    if max(load)<=1+1e-10:G.append(core+guard)
G=np.asarray(G,float)
print('global states',len(G),flush=True)

L=[];INC=[]
for v in range(4):
    ee=[e for e,(u,z) in enumerate(END) if u==v or z==v]
    INC.append(ee)
    vals=[]
    for a,b,h in itertools.product(range(K[ee[0]]+1),range(K[ee[1]]+1),(0,1)):
        if a*W[ee[0]]+b*W[ee[1]]+h*H[v]<=1+1e-10:vals.append((a,b,h))
    L.append(np.asarray(vals,float))
print('local states',[len(x) for x in L],flush=True)

OFF=np.cumsum([0]+[len(x) for x in L]);N=OFF[-1]
EQ=np.zeros((8,N));RHS=np.r_[np.ones(4),np.zeros(4)]
for v in range(4):EQ[v,OFF[v]:OFF[v+1]]=1
for e,(u,v) in enumerate(END):
    iu=INC[u].index(e);iv=INC[v].index(e)
    EQ[4+e,OFF[u]:OFF[u+1]]=L[u][:,iu]
    EQ[4+e,OFF[v]:OFF[v+1]]=-L[v][:,iv]

def val(q):
    rew=np.zeros(N)
    for v in range(4):
      for j,e in enumerate(INC[v]):
        if END[e][0]==v:rew[OFF[v]:OFF[v+1]]+=q[e]*L[v][:,j]
      rew[OFF[v]:OFF[v+1]]+=q[4+v]*L[v][:,2]
    ans=linprog(-rew,A_eq=EQ,b_eq=RHS,bounds=(0,None),method='highs')
    if not ans.success:raise RuntimeError(ans.message)
    glob=max(G@q)
    return (-ans.fun)/glob,ans.x,glob

rng=np.random.default_rng(390227)
best=(1,None)
for i in range(3000):
    q=np.exp(rng.uniform(-4,4,8))
    if i%2==0:q[rng.choice(8,size=rng.integers(1,5),replace=False)]=0
    if i%5==0:q[4:]=np.exp(rng.uniform(-2,2,4))
    r,lam,glob=val(q)
    if r>best[0]+1e-8:
        best=(r,{'q':q.tolist(),'iteration':i,'global_profit':glob})
        print('best',best,flush=True)
print('FINAL',best,flush=True)
