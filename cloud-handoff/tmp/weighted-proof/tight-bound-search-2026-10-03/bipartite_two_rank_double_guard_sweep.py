"""Two-rank graded path with a guard accepting two lower-rank edges.

Both core ranks descend by 1/CAP between adjacent path vertices.
Guards: 1-A, 1-B, and 1-2B (the last remains heavy for B<1/4).
"""
import json
import numpy as np
from scipy.optimize import linprog

CAP=10000
rng=np.random.default_rng(2026100307)

def build(a,b):
    guards=[0,CAP-a,CAP-b,CAP-2*b]
    nodes=[(i,j) for i in range(CAP//a+1) for j in range(CAP//b+1)]
    index={v:k for k,v in enumerate(nodes)}
    states=[]
    for ai,bi in nodes:
        for ao,bo in nodes:
            for g in range(4):
                if (a+1)*ai+(b+1)*bi+a*ao+b*bo+guards[g]<=CAP:
                    states.append((ai,bi,ao,bo,g))
    p=np.array([[s[2],s[3]]+[int(s[4]==g) for g in (1,2,3)] for s in states],float)
    leq=np.vstack([np.ones(len(states)),
                   np.array([s[0]-s[2] for s in states],float),
                   np.array([s[1]-s[3] for s in states],float)])
    geq=np.zeros((len(nodes)+1,len(states)));geq[0,:]=1
    for j,s in enumerate(states):
        geq[1+index[(s[0],s[1])],j]+=1
        geq[1+index[(s[2],s[3])],j]-=1
    return states,p,leq,geq,np.array([1,0,0],float),np.r_[1,np.zeros(len(nodes))]

def main():
    best=(4/3,None)
    for a in (3500,4100,4700):
        for b in (2100,2300):
            states,p,leq,geq,lrhs,grhs=build(a,b)
            localbest=(1,None)
            for t in range(2500):
                profit=np.exp(rng.uniform(-3,3,5))
                if t%4==0:profit[rng.integers(5)]=0
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
