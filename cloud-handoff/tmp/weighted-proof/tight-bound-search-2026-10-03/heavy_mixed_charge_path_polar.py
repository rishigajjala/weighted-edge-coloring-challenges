"""Full-profit polar diagnostic for a charge-violating heavy mixed bin.

Path core A=.251 (rank 3), C=.07 (rank 14); root guard .749 pairs A,
middle guard .67 fits A+C, terminal guard .94 rejects C. All types are
repeatable. The local vertex LP maximizes profit over coupled means and the
global polar inequalities normalize every physically feasible color.
"""
import itertools
import numpy as np
from scipy.optimize import linprog
from scipy.spatial import HalfspaceIntersection

WA,WC=.251,.07
H=(.749,.67,.94)
PA=[];L=[]
for a,c,g0,g1,g2 in itertools.product(range(4),range(15),(0,1),(0,1),(0,1)):
    if WA*a+H[0]*g0<=1+1e-10 and WA*a+WC*c+H[1]*g1<=1+1e-10 and WC*c+H[2]*g2<=1+1e-10:
        PA.append((a,c,g0,g1,g2))
P=np.unique(np.asarray(PA,float),axis=0)
for v in range(3):
    vals=[]
    for a,c,g in itertools.product(range(4),range(15),(0,1)):
        if v==0:
            if c==0 and WA*a+H[v]*g<=1+1e-10:vals.append((a,g))
        elif v==1:
            if WA*a+WC*c+H[v]*g<=1+1e-10:vals.append((a,c,g))
        else:
            if a==0 and WC*c+H[v]*g<=1+1e-10:vals.append((c,g))
    L.append(np.unique(np.asarray(vals,float),axis=0))
print('global/local patterns',len(P),[len(x) for x in L],flush=True)

n0,n1,n2=map(len,L);N=n0+n1+n2
EQ=np.zeros((5,N));RHS=np.array([1,1,1,0,0],float)
EQ[0,:n0]=1;EQ[1,n0:n0+n1]=1;EQ[2,n0+n1:]=1
EQ[3,:n0]=L[0][:,0];EQ[3,n0:n0+n1]=-L[1][:,0]
EQ[4,n0:n0+n1]=L[1][:,1];EQ[4,n0+n1:]=-L[2][:,0]
def local(q):
    reward=np.r_[L[0][:,0]*q[0]+L[0][:,1]*q[2],
                 L[1][:,1]*q[1]+L[1][:,2]*q[3],
                 L[2][:,1]*q[4]]
    ans=linprog(-reward,A_eq=EQ,b_eq=RHS,bounds=(0,None),method='highs')
    if not ans.success:raise RuntimeError(ans.message)
    return -ans.fun,ans.x
half=np.vstack([np.c_[P,-np.ones(len(P))],np.c_[-np.eye(5),np.zeros(5)]])
q0=np.full(5,1/(max(P.sum(axis=1))+2))
Q=np.unique(np.round(HalfspaceIntersection(half,q0).intersections,10),axis=0)
print('polar vertices',len(Q),flush=True)
best=(0,None)
for i,q in enumerate(Q):
    val,lam=local(q)
    if val>best[0]+1e-9:
        x=[lam[:n0]@L[0][:,0],lam[n0:n0+n1]@L[1][:,1],
           lam[:n0]@L[0][:,1],lam[n0:n0+n1]@L[1][:,2],
           lam[n0+n1:]@L[2][:,1]]
        best=(val,{'q':q.tolist(),'x':[float(z) for z in x],'index':i})
        print('best',best,flush=True)
print('FINAL',best,flush=True)
