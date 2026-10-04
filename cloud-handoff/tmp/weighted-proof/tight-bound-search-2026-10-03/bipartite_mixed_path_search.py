"""Exploratory fractional gap search on mixed-weight caterpillars.

This is a finite diagnostic only. Every pattern includes repeated copies of
an edge type, so any reported color upper support is for physical multigraphs.
"""
import os, sys, time, itertools, json
sys.path.insert(0, os.path.abspath('tmp/lower-search-deps'))
import numpy as np
from scipy.optimize import linprog
from scipy.spatial import ConvexHull

RNG = np.random.default_rng(20261003)
CAP = 12

def patterns(edges, weights, nv):
    rem = [CAP] * nv
    z = [0] * len(edges)
    out = []
    def rec(i):
        if i == len(edges):
            if all(min(rem[u], rem[v]) < w for (u,v),w in zip(edges,weights)):
                out.append(z.copy())
            return
        u,v = edges[i]; w = weights[i]
        for k in range(min(rem[u],rem[v])//w+1):
            z[i] = k; rem[u] -= k*w; rem[v] -= k*w
            rec(i+1)
            rem[u] += k*w; rem[v] += k*w
    rec(0)
    return np.asarray(out, dtype=float)

def local_ineq(edges, weights, nv):
    aa=[]; bb=[]
    for v in range(nv):
        idx=[i for i,e in enumerate(edges) if v in e]
        if not idx: continue
        ww=[weights[i] for i in idx]
        pts=np.asarray([x for x in itertools.product(*[range(CAP//w+1) for w in ww]) if sum(a*b for a,b in zip(x,ww))<=CAP], dtype=float)
        if len(idx)==1:
            a=np.zeros(len(edges));a[idx[0]]=1;aa.append(a);bb.append(CAP//ww[0]);continue
        hull=ConvexHull(pts)
        seen=set()
        for eq in hull.equations:
            if max(eq[:-1]) <= 1e-9:continue
            key=tuple(np.round(eq,9))
            if key in seen:continue
            seen.add(key)
            a=np.zeros(len(edges));a[idx]=eq[:-1];aa.append(a);bb.append(-eq[-1])
    return np.asarray(aa),np.asarray(bb)

def score(edges,weights,nv,tries=6):
    pats=patterns(edges,weights,nv)
    a,b=local_ineq(edges,weights,nv)
    best=1.; result=None
    for trial in range(tries):
        p=RNG.exponential(size=len(edges))
        last=0
        for k in range(20):
            loc=linprog(-p,A_ub=a,b_ub=b,bounds=(0,None),method='highs')
            if not loc.success:raise ValueError(loc.message)
            d=loc.x
            glob=linprog(-d,A_ub=pats,b_ub=np.ones(len(pats)),bounds=(0,None),method='highs')
            if not glob.success:raise ValueError(glob.message)
            val=-glob.fun;p=glob.x
            if val>best+1e-8:best=val;result=(d.tolist(),p.tolist(),len(pats))
            if val<last+1e-8:break
            last=val
    return best,result

def main():
    best=4/3
    sizes=[4,5,6,7,8,9,12]
    start=time.time()
    for it in range(600):
        m=int(RNG.integers(2,7))
        edges=[(i,i+1) for i in range(m)]
        edges += [(i,m+1+i) for i in range(m+1)]
        weights=RNG.choice(sizes,size=len(edges)).tolist()
        try: val,data=score(edges,weights,2*m+2)
        except Exception as ex:
            print('ERR',it,str(ex),flush=True);continue
        if val>best+1e-7:
            best=val
            item={'iteration':it,'ratio':val,'edges':edges,'weights':weights,'demand':data[0],'dual':data[1],'patterns':data[2]}
            print('BEST',json.dumps(item),flush=True)
            with open('tmp/weighted-proof/tight-bound-search-2026-10-03/bipartite_mixed_path_best.json','w') as f:json.dump(item,f,indent=2)
        if it%50==0:print('PROGRESS',it,'best',best,'seconds',round(time.time()-start,1),flush=True)

if __name__=='__main__':main()
