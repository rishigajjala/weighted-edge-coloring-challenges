"""Probe the half-overflow claim for independent singleton leaves plus one private double leaf pair."""
import itertools
import math


def poibin(ps):
    d=[1.]
    for p in ps:
        z=[0.]*(len(d)+1)
        for k,v in enumerate(d):
            z[k]+=v*(1-p)
            z[k+1]+=v*p
        d=z
    return d


def min_overflow(ps,x,q):
    sd=poibin(ps)
    atoms=[]
    for k,v in enumerate(sd):
        atoms.append((k-1,v*x))
        atoms.append((k,v*(1-x)))
    atoms.sort()
    rem=q
    loss=0.
    for d,m in atoms:
        take=min(rem,m)
        loss+=take*max(0,d+2)+(m-take)*max(0,d)
        rem-=take
    return loss


if __name__=='__main__':
    best=(0,None)
    grid=[i/20 for i in range(1,20)]
    for n in range(1,10):
        for p in grid:
            s=n*p
            for x in grid+[1.]:
                if s>x: continue
                for q in grid:
                    if s+2*q>x+1e-12: continue
                    v=min_overflow([p]*n,x,q)
                    if v>best[0]: best=(v,(n,p,x,q))
    print(best)
