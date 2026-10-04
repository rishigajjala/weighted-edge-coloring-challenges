"""Stationary diagnostic for one guard shared by rank-2 A and rank-4 B.

The guard fits either one outgoing A or two outgoing B, but not the
corresponding incoming combination. A is approximately 2B.
"""

import json
import numpy as np
from scipy.optimize import linprog

CAP = 12000
AIN, AOUT = 5762, 5760
BIN, BOUT = 2881, 2880
GUARD = CAP - AOUT
NODES = [(a,b) for a in range(3) for b in range(5)]
NODE_INDEX = {v:i for i,v in enumerate(NODES)}
STATES=[]
for ai,bi in NODES:
    for ao,bo in NODES:
        for g in (0,1):
            if AIN*ai+BIN*bi+AOUT*ao+BOUT*bo+GUARD*g<=CAP:
                STATES.append((ai,bi,ao,bo,g))
P=np.array([[s[2],s[3],s[4]] for s in STATES],float)
LOCAL_EQ=np.vstack([np.ones(len(STATES)),
                    np.array([s[0]-s[2] for s in STATES],float),
                    np.array([s[1]-s[3] for s in STATES],float)])
LOCAL_RHS=np.array([1,0,0],float)
FLOW_EQ=np.zeros((len(NODES)+1,len(STATES)),float)
FLOW_EQ[0,:]=1
for j,s in enumerate(STATES):
    FLOW_EQ[1+NODE_INDEX[(s[0],s[1])],j]+=1
    FLOW_EQ[1+NODE_INDEX[(s[2],s[3])],j]-=1
FLOW_RHS=np.zeros(len(NODES)+1);FLOW_RHS[0]=1


def values(profit,reverse_b=False):
    reward=P@profit
    loc=linprog(-reward,A_eq=LOCAL_EQ,b_eq=LOCAL_RHS,
                bounds=(0,None),method='highs')
    if not loc.success:raise RuntimeError(loc.message)
    if reverse_b:
        flow=np.zeros_like(FLOW_EQ);flow[0,:]=1
        for j,s in enumerate(STATES):
            flow[1+NODE_INDEX[(s[0],s[3])],j]+=1
            flow[1+NODE_INDEX[(s[2],s[1])],j]-=1
    else:flow=FLOW_EQ
    glob=linprog(-reward,A_eq=flow,b_eq=FLOW_RHS,
                 bounds=(0,None),method='highs')
    if not glob.success:raise RuntimeError(glob.message)
    return -loc.fun,-glob.fun,loc.x,glob.x


def main():
    print('MODEL',json.dumps({'weights':[AIN,AOUT,BIN,BOUT,GUARD],
                              'states':len(STATES),'nodes':len(NODES)}),flush=True)
    rng=np.random.default_rng(2026100311)
    for reverse_b in (False,True):
        best=(0,None)
        for it in range(4000):
            p=np.exp(rng.uniform(-4,4,size=3))
            if it%6==0:p[rng.integers(0,3)]=0
            loc,glob,lx,gx=values(p,reverse_b)
            ratio=loc/glob if glob else 1
            if ratio>best[0]+1e-7:
                best=(ratio,dict(iteration=it,ratio=ratio,profit=p.tolist(),
                                 local_value=loc,global_value=glob,
                                 local_support=[(STATES[j],float(q)) for j,q in enumerate(lx) if q>1e-7],
                                 global_support=[(STATES[j],float(q)) for j,q in enumerate(gx) if q>1e-7]))
                print('BEST',reverse_b,json.dumps(best[1]),flush=True)
        print('FINAL',reverse_b,json.dumps(best[1]),flush=True)


if __name__=='__main__':main()
