"""Two-rank graded-path stationary local/global hull diagnostic.

Core types A~5/12 (>1/3) and B~4/15 (between 1/4 and 1/3) both
decrease along the path. Heavy guards complement each outgoing type.
Local LP balances only means; stationary LP balances every full count
state. Random nonnegative profits expose potential gaps.
"""
import json

import numpy as np
from scipy.optimize import linprog

CAP=6000
AIN,AOUT=2501,2500
BIN,BOUT=1601,1600
GA,GB=CAP-AOUT,CAP-BOUT
MAXA=CAP//AOUT
MAXB=CAP//BOUT
NODES=[(a,b) for a in range(MAXA+1) for b in range(MAXB+1)]
NODE_INDEX={v:i for i,v in enumerate(NODES)}
STATES=[]
for ai,bi in NODES:
    for ao,bo in NODES:
        for guard in (0,1,2):
            load=AIN*ai+BIN*bi+AOUT*ao+BOUT*bo+(GA if guard==1 else GB if guard==2 else 0)
            if load<=CAP:
                STATES.append((ai,bi,ao,bo,guard))
P=np.array([[s[2],s[3],int(s[4]==1),int(s[4]==2)] for s in STATES],dtype=float)
LOCAL_EQ=np.vstack([np.ones(len(STATES)),
                    np.array([s[0]-s[2] for s in STATES],dtype=float),
                    np.array([s[1]-s[3] for s in STATES],dtype=float)])
LOCAL_RHS=np.array([1,0,0],dtype=float)
FLOW_EQ=np.zeros((len(NODES)+1,len(STATES)),dtype=float)
FLOW_EQ[0,:]=1
for j,s in enumerate(STATES):
    FLOW_EQ[1+NODE_INDEX[(s[0],s[1])],j]+=1
    FLOW_EQ[1+NODE_INDEX[(s[2],s[3])],j]-=1
FLOW_RHS=np.zeros(len(NODES)+1);FLOW_RHS[0]=1

def values(profit):
    reward=P@profit
    loc=linprog(-reward,A_eq=LOCAL_EQ,b_eq=LOCAL_RHS,bounds=(0,None),method='highs')
    glob=linprog(-reward,A_eq=FLOW_EQ,b_eq=FLOW_RHS,bounds=(0,None),method='highs')
    if not loc.success or not glob.success:
        raise RuntimeError((loc.message,glob.message))
    return -loc.fun,-glob.fun,loc.x,glob.x

def main():
    print('MODEL',json.dumps({'capacity':CAP,'weights':[AIN,AOUT,BIN,BOUT,GA,GB],
                              'nodes':len(NODES),'states':len(STATES)}),flush=True)
    rng=np.random.default_rng(2026100305)
    best=(1.0,None)
    for it in range(6000):
        p=np.exp(rng.uniform(-4,4,size=4))
        if it%5==0:
            p[rng.integers(0,4)]=0
        loc,glob,lx,gx=values(p)
        ratio=loc/glob if glob>0 else 1
        if ratio>best[0]+1e-7:
            best=(ratio,{'iteration':it,'ratio':ratio,'profit':p.tolist(),
                         'local_value':loc,'global_value':glob,
                         'local_support':[(STATES[i],float(x)) for i,x in enumerate(lx) if x>1e-7],
                         'global_support':[(STATES[i],float(x)) for i,x in enumerate(gx) if x>1e-7]})
            print('BEST',json.dumps(best[1]),flush=True)
        if it%500==0:
            print('PROGRESS',it,'best',best[0],flush=True)
    print('FINAL',json.dumps(best[1]),flush=True)

if __name__=='__main__':main()
