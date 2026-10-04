"""Adversarial numerical test of Jensen-sufficient K=3 expected-max bound."""

import argparse
from itertools import product

import numpy as np
from scipy.optimize import differential_evolution


def gap(x, m, n, K=3):
    y=x[0]
    au=np.array(x[1:1+m]); av=np.array(x[1+m:1+m+n])
    i=1+m+n
    if y+au.sum()>1 or y+av.sum()>1:
        return 2+max(y+au.sum()-1,y+av.sum()-1)
    du=y+au.sum()+(1-y-au.sum())*x[i]; i+=1
    dv=y+av.sum()+(1-y-av.sum())*x[i]; i+=1
    pu=(1+3*du)/4; pv=(1+3*dv)/4
    if pu*pv<K/12:
        return 2+K/12-pu*pv
    ru=(1+3*(au+(1-au)*np.array(x[i:i+m])))/4; i+=m
    rv=(1+3*(av+(1-av)*np.array(x[i:i+n])))/4
    bu=au/(pu*ru); bv=av/(pv*rv)
    bb=y/(pu*pv)
    bitsu=np.array(list(product([0.,1.],repeat=m)))
    bitsv=np.array(list(product([0.,1.],repeat=n)))
    qu=np.prod(np.where(bitsu>0,ru,1-ru),axis=1)
    qv=np.prod(np.where(bitsv>0,rv,1-rv),axis=1)
    xu=bitsu@bu; xv=bitsv@bv
    den=np.maximum.reduce([np.full((len(xu),len(xv)),1/K),
                           bb+xu[:,None]+np.zeros((1,len(xv))),
                           bb+xv[None,:]+np.zeros((len(xu),1))])
    return 4/3-(qu[:,None]*qv[None,:]*den).sum()


if __name__=='__main__':
    pa=argparse.ArgumentParser();pa.add_argument('--spokes',type=int,default=3)
    pa.add_argument('--maxiter',type=int,default=1000)
    args=pa.parse_args();m=n=args.spokes
    bounds=[(1e-8,.999999)]+[(0,1)]*(m+n+2+m+n)
    opt=differential_evolution(lambda x:gap(x,m,n),bounds,popsize=12,
                               maxiter=args.maxiter,seed=9396,polish=True,tol=1e-10)
    print('min gap',opt.fun,'params',opt.x,'evals',opt.nfev)
