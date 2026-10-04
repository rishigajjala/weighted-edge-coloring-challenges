"""Targeted two-period stationary local/global diagnostic.

Core weights alternate 0.34 (rank 2) and 0.26 (rank 3).  A guard of
weight 0.74 rejects an incoming 0.34 but fits one outgoing 0.26;
the reverse guard 0.66 fits one outgoing 0.34 but rejects a *pair* of
incoming 0.26 edges.  This tests count-state reversal across ranks,
not a monotone complementary-guard path.  Output is diagnostic only.
"""
import itertools
import json
import numpy as np
from scipy.optimize import linprog

W = (0.34, 0.26)
H = (0.66, 0.74)
K = tuple(int(1 / w + 1e-9) for w in W)
states = []
for i in range(2):
    prev = (i - 1) % 2
    ss = []
    for a, b, g in itertools.product(range(K[prev]+1), range(K[i]+1), (0, 1)):
        if a*W[prev]+b*W[i]+g*H[i] <= 1+1e-10:
            ss.append((a,b,g))
    states.append(ss)
offs = (0, len(states[0]), len(states[0])+len(states[1]))
n = offs[-1]
Q = np.zeros((4,n))
mass = np.zeros((2,n))
mean = np.zeros((2,n))
hist = np.zeros((sum(k+1 for k in K),n))
for i in range(2):
    for j,(a,b,g) in enumerate(states[i]):
        col=offs[i]+j
        mass[i,col]=1
        Q[i,col]=b
        Q[2+i,col]=g
        mean[i,col]+=b
        mean[(i-1)%2,col]-=a
        hist[sum(K[t]+1 for t in range(i))+b,col]+=1
        prev=(i-1)%2
        hist[sum(K[t]+1 for t in range(prev))+a,col]-=1
L_eq=np.vstack([mass,mean]);L_rhs=np.r_[np.ones(2),np.zeros(2)]
G_eq=np.vstack([mass,hist]);G_rhs=np.r_[np.ones(2),np.zeros(hist.shape[0])]

def solve(profit,glob=False):
    A=G_eq if glob else L_eq
    b=G_rhs if glob else L_rhs
    res=linprog(-(profit@Q),A_eq=A,b_eq=b,bounds=(0,None),method="highs")
    if not res.success: raise RuntimeError(res.message)
    return -res.fun,res.x

if __name__=="__main__":
    rng=np.random.default_rng(20261003)
    best=(0,None)
    for t in range(30000):
        p=rng.exponential(size=4)
        if t%7==0: p[rng.integers(0,4)]=0
        l,x=solve(p)
        g,z=solve(p,True)
        if g>1e-12 and l/g>best[0]+1e-10:
            best=(l/g,p.tolist())
            print(json.dumps({"trial":t,"ratio":l/g,"profit":p.tolist(),
                "local":l,"global":g,
                "local_states":[[list(states[i][j]),float(x[offs[i]+j])]
                    for i in range(2) for j in range(len(states[i])) if x[offs[i]+j]>1e-8],
                "global_states":[[list(states[i][j]),float(z[offs[i]+j])]
                    for i in range(2) for j in range(len(states[i])) if z[offs[i]+j]>1e-8]}),flush=True)
    print("final best",best,flush=True)
