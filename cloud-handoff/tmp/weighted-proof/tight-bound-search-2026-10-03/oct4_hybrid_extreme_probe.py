import math
import random

import numpy as np
from scipy.optimize import linprog

from oct4_hybrid_branch_probe import recourse


def run(seed=9271, trials=5000):
    rng = random.Random(seed)
    best = (float("inf"), None)
    for t in range(trials):
        k = rng.choice([2, 3, 4])
        n = 2*k
        pairs = [(2*i, 2*i+1) for i in range(k)]
        verts = list(range(n))
        rng.shuffle(verts)
        edges = []
        for j in range(1,n):
            edges.append(tuple(sorted((verts[j], verts[rng.randrange(j)]))))
        if rng.random() < .4:
            extras = [(u,v) for u in range(n) for v in range(u+1,n) if (u,v) not in edges]
            rng.shuffle(extras)
            edges += extras[:rng.choice([1,2])]
        m = len(edges)
        D = [rng.uniform(.05,1) for _ in pairs]
        q = [10**rng.uniform(-.5,.5) for _ in edges]
        A = np.zeros((n,m))
        for j,(u,v) in enumerate(edges):
            A[u,j]=A[v,j]=1
        opt = linprog(-np.array(q),A_ub=A,b_ub=np.array([D[v//2] for v in range(n)]),bounds=[(0,None)]*m,method="highs")
        assert opt.success
        y=opt.x
        if sum(y)<1e-7: continue
        edges=[edges[j] for j in range(m) if y[j]>1e-7]
        q=[q[j] for j in range(m) if y[j]>1e-7]
        y=[float(v) for v in y if v>1e-7]
        C=[12*v for v in y]
        p=[(1+2*d)/3 for d in D]
        values=[]
        for mask in range(1<<k):
            active=[bool(mask&(1<<i)) for i in range(k) for _ in range(2)]
            values.append(recourse(edges,C,q,active,n))
        ind=sum(values[mask]*math.prod(p[i] if mask&(1<<i) else 1-p[i] for i in range(k)) for mask in range(1<<k))
        cuts=sorted(set([0.,1.]+p))
        com=sum((b-a)*values[sum(1<<i for i in range(k) if (a+b)/2<=p[i])] for a,b in zip(cuts,cuts[1:]))
        target=sum(a*b for a,b in zip(q,y))
        ratio=(.75*ind+.25*com)/target
        if ratio<best[0]:
            best=(ratio,dict(t=t,edges=edges,D=D,y=y,q=q,ind=ind/target,com=com/target))
            print(best,flush=True)


if __name__=="__main__":
    run()
