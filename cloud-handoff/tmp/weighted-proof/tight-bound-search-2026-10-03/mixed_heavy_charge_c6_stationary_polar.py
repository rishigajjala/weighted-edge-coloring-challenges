"""Exact symmetric-profit polar on an alternating rank-3/rank-4 C6.

Three lax factor vertices have guard .54, which fits A=.251+B=.201.
Three strict blocker vertices have guard .79, which fits B but rejects A.
All six light edge types are physically present; aggregate profits and demands
are rotation-by-two symmetric. This tests an odd three-factor relation cycle
inside a bipartite six-cycle, not merely a single charge-violating hub.
"""
import itertools
import numpy as np
from scipy.optimize import linprog
from scipy.spatial import HalfspaceIntersection

A,B=.251,.201
HL,HS=.54,.79
L=[];S=[]
for a,b,h in itertools.product(range(4),range(5),(0,1)):
    if A*a+B*b+HL*h<=1+1e-10:L.append((a,b,h))
    if A*a+B*b+HS*h<=1+1e-10:S.append((a,b,h))
L=np.asarray(L,float);S=np.asarray(S,float)
print('local patterns',len(L),len(S),flush=True)

P=set()
for ca in itertools.product(range(4),repeat=3):
 for cb in itertools.product(range(5),repeat=3):
  core=(ca[0],cb[0],ca[1],cb[1],ca[2],cb[2])
  load=[A*core[i-1]+B*core[i] if i%2==0 else A*core[i-1]+B*core[i]
        for i in range(6)]
  # The two incident weights are always A and B; edge i has A for even i.
  load=[(A if (i-1)%2==0 else B)*core[i-1]
        +(A if i%2==0 else B)*core[i] for i in range(6)]
  if max(load)>1+1e-10:continue
  for mask in range(64):
   ok=True;gl=gs=0
   for i in range(6):
    h=(mask>>i)&1
    if load[i]+h*(HL if i%2==0 else HS)>1+1e-10:ok=False;break
    if i%2==0:gl+=h
    else:gs+=h
   if ok:P.add((sum(ca),sum(cb),gl,gs))
P=np.asarray(sorted(P),float)
print('aggregate global patterns',len(P),flush=True)

nL,nS=len(L),len(S)
EQ=np.zeros((4,nL+nS));RHS=np.array([1,1,0,0],float)
EQ[0,:nL]=1;EQ[1,nL:]=1
EQ[2,:nL]=L[:,0];EQ[2,nL:]=-S[:,0]
EQ[3,:nL]=L[:,1];EQ[3,nL:]=-S[:,1]
def local(q):
    rew=np.r_[3*(L[:,0]*q[0]+L[:,1]*q[1]+L[:,2]*q[2]),
              3*S[:,2]*q[3]]
    ans=linprog(-rew,A_eq=EQ,b_eq=RHS,bounds=(0,None),method='highs')
    if not ans.success:raise RuntimeError(ans.message)
    return -ans.fun,ans.x

half=np.vstack([np.c_[P,-np.ones(len(P))],np.c_[-np.eye(4),np.zeros(4)]])
q0=np.full(4,1/(max(P.sum(axis=1))+2))
Q=np.unique(np.round(HalfspaceIntersection(half,q0).intersections,10),axis=0)
print('polar vertices',len(Q),flush=True)
best=(0,None)
for i,q in enumerate(Q):
 val,lam=local(q)
 if val>best[0]+1e-8:
  x=[lam[:nL]@L[:,0],lam[:nL]@L[:,1],lam[:nL]@L[:,2],lam[nL:]@S[:,2]]
  best=(val,{'q':q.tolist(),'local_mean':[float(z) for z in x],'index':i})
  print('best',best,flush=True)
print('FINAL',best,flush=True)
