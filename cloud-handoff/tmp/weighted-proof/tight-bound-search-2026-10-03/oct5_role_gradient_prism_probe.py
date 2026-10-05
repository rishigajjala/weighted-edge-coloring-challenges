"""Targeted two-layer rank-shifting port prism; diagnostic, not certificate."""
import argparse
import itertools
import numpy as np
from oct5_port_profit_polar_probe import polar
from scipy.optimize import milp, Bounds, LinearConstraint


def matchings(seq):
    if not seq:
        yield ()
        return
    a = seq[0]
    for j in range(1, len(seq)):
        b = seq[j]
        for rest in matchings(seq[1:j] + seq[j+1:]):
            yield ((a,b),) + rest


def make(ml, mr):
    # A_i shore parity i, B_i opposite shore. Cyclic adjacent weights climb
    # then descend; each port's third edge completes its unit-weight row.
    a = np.array([.27,.29,.31,.31,.29,.27])
    ports = [(layer,i) for layer in range(2) for i in range(6)]
    left = [p for p in ports if (p[0]+p[1]) % 2 == 0]
    right = [p for p in ports if (p[0]+p[1]) % 2 == 1]
    li = {p:j for j,p in enumerate(left)}
    ri = {p:j for j,p in enumerate(right)}
    edges = []
    def add(p,q,w):
        if p in li:edges.append((li[p],ri[q],w))
        else:edges.append((li[q],ri[p],w))
    for layer in range(2):
        for i in range(6):add((layer,i),(layer,(i+1)%6),a[i])
    for i in range(6):add((0,i),(1,i),1-a[(i-1)%6]-a[i])
    w=np.array([e[2] for e in edges]); triples=[(e[0],e[1]) for e in edges]
    ol=np.empty(6,dtype=int);orr=np.empty(6,dtype=int)
    for i,(u,v) in enumerate(ml):ol[u]=ol[v]=i
    for i,(u,v) in enumerate(mr):orr[u]=orr[v]=i
    return w,triples,ol,orr


def best_phase(w,triples,ol,orr):
    out=0
    for ml in itertools.product([0,1],repeat=3):
        active_l={u for i,(u,v) in enumerate(LMATCH) for u in [((u,v)[ml[i]])]}
        for mr in itertools.product([0,1],repeat=3):
            active_r={u for i,(u,v) in enumerate(RMATCH) for u in [((u,v)[mr[i]])]}
            val=sum(w[j] for j,(u,v) in enumerate(triples) if u in active_l and v in active_r)
            out=max(out,val)
    return out


def support(w,triples,ol,orr):
    B=np.zeros((6,len(w)))
    for j,(u,v) in enumerate(triples):B[ol[u],j]=w[j];B[3+orr[v],j]=w[j]
    sol=milp(-w,integrality=np.ones(len(w)),bounds=Bounds(np.zeros(len(w)),np.floor(1/w)),
             constraints=LinearConstraint(B,-np.inf,np.ones(6)),options={"time_limit":5})
    return -sol.fun if sol.status==0 else None


if __name__=='__main__':
    p=argparse.ArgumentParser();p.add_argument('--polar',type=int,default=8);args=p.parse_args()
    candidates=[]
    allm=list(matchings(tuple(range(6))))
    for LMATCH in allm:
        for RMATCH in allm:
            w,t,ol,orr=make(LMATCH,RMATCH)
            phase=best_phase(w,t,ol,orr)
            candidates.append((phase,LMATCH,RMATCH,w,t,ol,orr))
    candidates.sort(key=lambda r:r[0])
    print('minimum phase-only max',candidates[0][0],'local target',3,flush=True)
    seen=set();n=0
    for phase,LMATCH,RMATCH,w,t,ol,orr in candidates:
        key=(LMATCH,RMATCH)
        if key in seen:continue
        seen.add(key)
        weight_max=support(w,t,ol,orr)
        val,it,cert=polar(w,t,ol,orr,limit=200)
        print('phase',phase,'weight max',weight_max,'polar',val,'iters',it,'pairings',LMATCH,RMATCH,flush=True)
        n+=1
        if n>=args.polar:break
