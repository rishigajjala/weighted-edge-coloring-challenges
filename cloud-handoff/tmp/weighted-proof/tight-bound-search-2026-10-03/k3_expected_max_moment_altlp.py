"""Alternating moment-LP search for the K=3 Jensen-sufficient bound."""

import argparse
import numpy as np
from scipy.optimize import linprog


def moments(d,y):
    p=(1+3*d)/4;s=d-y
    t=min(s,1/3);h=3*t*(1-t)/(1+3*t)
    return s/p,s*h/p**2


def maximize(du,dv,y,grid,starts=2,steps=12,rng=None):
    pu,pv=(1+3*du)/4,(1+3*dv)/4
    if pu*pv<.25:return None
    b=y/(pu*pv)
    mus=[];var=[]
    for d in [du,dv]:
        m,v=moments(d,y);mus.append(m);var.append(v)
    g=np.maximum.reduce([np.full((len(grid),len(grid)),1/3),
                         b+grid[:,None]+np.zeros((1,len(grid))),
                         b+grid[None,:]+np.zeros((len(grid),1))])
    constr=[]
    for m,v in zip(mus,var):
        constr.append((np.array([grid**2]),np.array([m*m+v+1e-11]),
                       np.array([np.ones(len(grid)),grid]),np.array([1,m])))
    best=(-1,None)
    for k in range(starts):
        q=np.zeros(len(grid))
        if k==0:
            j=np.searchsorted(grid,mus[1]);j=min(max(1,j),len(grid)-1)
            q[j-1]=(grid[j]-mus[1])/(grid[j]-grid[j-1]);q[j]=1-q[j-1]
        else:
            c=rng.random(len(grid))
            z=linprog(-c,A_ub=constr[1][0],b_ub=constr[1][1],A_eq=constr[1][2],b_eq=constr[1][3],bounds=(0,None),method='highs')
            q=z.x if z.success else q
        p=None
        for _ in range(steps):
            z=linprog(-(g@q),A_ub=constr[0][0],b_ub=constr[0][1],A_eq=constr[0][2],b_eq=constr[0][3],bounds=(0,None),method='highs')
            if not z.success:break
            p=z.x
            z=linprog(-(p@g),A_ub=constr[1][0],b_ub=constr[1][1],A_eq=constr[1][2],b_eq=constr[1][3],bounds=(0,None),method='highs')
            if not z.success:break
            q=z.x
        if p is None:continue
        val=p@g@q
        if val>best[0]:best=(val,(p,q))
    return best[0],b,mus,var,best[1]


if __name__=='__main__':
    pa=argparse.ArgumentParser();pa.add_argument('--trials',type=int,default=1000)
    pa.add_argument('--grid',type=int,default=81)
    args=pa.parse_args();grid=np.linspace(0,4,args.grid)
    rng=np.random.default_rng(9396);best=(-1,None)
    for k in range(args.trials):
        du,dv=rng.random(2);y=min(du,dv)*rng.random()
        z=maximize(du,dv,y,grid,rng=rng)
        if z is None:continue
        if z[0]>best[0]:
            best=(z[0],(du,dv,y,z[1:4]));print('record',k,best,flush=True)
        if best[0]>4/3+1e-5:break
    print('final',best)
