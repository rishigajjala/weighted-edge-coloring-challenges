"""Small structured diagnostic; not a proof of the fixed-law transfer."""
from itertools import product
from scipy.optimize import linprog
from functools import lru_cache
from collections import Counter

n=6
pairs=((0,1),(2,3),(4,5))
Dtuples=((.5,.5,.5),(.75,.5,.25),(1,.5,.5),(1,1,.5),(.75,.75,.75))

def tree_edges(seq):
    deg=[1]*n
    for v in seq:deg[v]+=1
    out=[]
    for v in seq:
        leaf=next(i for i in range(n) if deg[i]==1)
        out.append((min(leaf,v),max(leaf,v)))
        deg[leaf]-=1;deg[v]-=1
    rem=[i for i in range(n) if deg[i]==1]
    out.append(tuple(rem))
    return tuple(sorted(out))

def lp(E, deg, caps=None):
    A=[[int(v in e) for e in E] for v in range(n)]
    bounds=[(0,None if caps is None else caps[j]) for j in range(len(E))]
    r=linprog([-1]*len(E),A_ub=A,b_ub=deg,bounds=bounds,method='highs')
    if not r.success:raise RuntimeError(r.message)
    return -r.fun,r.x

def calc(E,ds):
    D=tuple(ds[j//2] for j in range(n))
    target,y=lp(E,D)
    caps=12*y
    p=tuple((1+2*d)/3 for d in ds)
    vals={}
    for B in product((0,1),repeat=3):
        deg=tuple(B[j//2] for j in range(n))
        vals[B]=lp(E,deg,caps)[0]
    ind=0
    for B,val in vals.items():
        prob=1
        for b,pi in zip(B,p):prob*=pi if b else 1-pi
        ind+=prob*val
    thresholds=sorted(set((0.,1.)+p))
    com=0
    for lo,hi in zip(thresholds,thresholds[1:]):
        u=(lo+hi)/2
        B=tuple(int(u<=pi) for pi in p)
        com+=(hi-lo)*vals[B]
    got=.75*ind+.25*com
    return got-(2/3)*target,(target,got,ind,com,y)

best=(1e9,None)
ct=0
for seq in product(range(n),repeat=n-2):
    E=tree_edges(seq)
    for ds in Dtuples:
        gap,detail=calc(E,ds)
        ct+=1
        if gap<best[0]:best=(gap,(E,ds,detail))
print('instances',ct,'best',best,flush=True)
