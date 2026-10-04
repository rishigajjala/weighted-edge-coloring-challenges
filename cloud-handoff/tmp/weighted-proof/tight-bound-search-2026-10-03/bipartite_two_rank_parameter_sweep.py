"""Heuristic sweep of two-core-rank graded-path transition models.

Local means balance A and B separately; global stationary schedules
balance their full count-vector distributions. Both heavy guards are
complements of the corresponding outgoing core weight.
"""
import json
import numpy as np
from scipy.optimize import linprog

CAP=10000
rng=np.random.default_rng(2026100306)

def build(a,b):
    nodes=[(i,j) for i in range(CAP//a+1) for j in range(CAP//b+1)]
    index={v:k for k,v in enumerate(nodes)}
    states=[]
    for ai,bi in nodes:
        for ao,bo in nodes:
            for g in (0,1,2):
                load=(a+1)*ai+(b+1)*bi+a*ao+b*bo+(CAP-a if g==1 else CAP-b if g==2 else 0)
                if load<=CAP:states.append((ai,bi,ao,bo,g))
    pmat=np.array([[s[2],s[3],int(s[4]==1),int(s[4]==2)] for s in states],float)
    leq=np.vstack([np.ones(len(states)),
                   np.array([s[0]-s[2] for s in states],float),
                   np.array([s[1]-s[3] for s in states],float)])
    geq=np.zeros((len(nodes)+1,len(states)));geq[0,:]=1
    for j,s in enumerate(states):
        geq[1+index[(s[0],s[1])],j]+=1
        geq[1+index[(s[2],s[3])],j]-=1
    lrhs=np.array([1,0,0],float)
    grhs=np.zeros(len(nodes)+1);grhs[0]=1
    return states,pmat,leq,geq,lrhs,grhs

def main():
    best=(4/3,None)
    for a in (3500,3900,4300,4700):
        for b in (2100,2300,2500,2700,2900,3100,3300):
            states,p,leq,geq,lrhs,grhs=build(a,b)
            localbest=(1,None)
            for t in range(350):
                profit=np.exp(rng.uniform(-3,3,4))
                if t%4==0:profit[rng.integers(4)]=0
                reward=p@profit
                l=linprog(-reward,A_eq=leq,b_eq=lrhs,bounds=(0,None),method='highs')
                g=linprog(-reward,A_eq=geq,b_eq=grhs,bounds=(0,None),method='highs')
                if not(l.success and g.success):raise RuntimeError((l.message,g.message))
                ratio=l.fun/g.fun
                if ratio>localbest[0]:localbest=(ratio,profit.tolist())
                if ratio>best[0]+1e-7:
                    best=(ratio,{'a':a,'b':b,'profit':profit.tolist(),
                                 'local':-l.fun,'global':-g.fun,'states':len(states)})
                    print('BEST',json.dumps(best[1]),flush=True)
            print('CASE',a,b,'states',len(states),'best',localbest[0],flush=True)
    print('FINAL',json.dumps({'best':best[1],'threshold':4/3}),flush=True)

if __name__=='__main__':main()
