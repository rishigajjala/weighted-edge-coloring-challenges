import argparse
from itertools import product

import numpy as np
from scipy.optimize import differential_evolution


def objective(x, m, n, bmin):
    y=x[0]
    a=x[1:1+m]
    c=x[1+m:1+m+n]
    a=(1-y)*a/max(1,a.sum())
    c=(1-y)*c/max(1,c.sum())
    i=1+m+n
    du=y+a.sum()+(1-y-a.sum())*x[i]
    dv=y+c.sum()+(1-y-c.sum())*x[i+1]
    i+=2
    pu=(1+3*du)/4;pv=(1+3*dv)/4
    b=(4/3)*y/(pu*pv)
    if b < bmin or b > 12*y:
        return 10+max(bmin-b,b-12*y)
    ru=(1+3*(a+(1-a)*x[i:i+m]))/4
    i+=m
    rv=(1+3*(c+(1-c)*x[i:i+n]))/4
    bu=np.minimum((4/3)*a/(pu*ru),12*a)
    bv=np.minimum((4/3)*c/(pv*rv),12*c)
    bitsu=np.array(list(product((0,1),repeat=m)))
    bitsv=np.array(list(product((0,1),repeat=n)))
    qu=np.prod(np.where(bitsu,ru,1-ru),axis=1)
    qv=np.prod(np.where(bitsv,rv,1-rv),axis=1)
    U=b+bitsu@bu
    V=b+bitsv@bv
    em=np.sum(qu[:,None]*qv[None,:]*np.maximum(U[:,None],V[None,:]))
    return -em


if __name__=='__main__':
    parser=argparse.ArgumentParser()
    parser.add_argument('--spokes',type=int,default=3)
    parser.add_argument('--bmin',type=float,default=32/81)
    parser.add_argument('--maxiter',type=int,default=700)
    parser.add_argument('--popsize',type=int,default=16)
    args=parser.parse_args()
    m=n=args.spokes
    bounds=[(.001,.999)]+[(0,1)]*(2*m+2*m+2)
    for seed in (83,971,1433):
        opt=differential_evolution(lambda x:objective(x,m,n,args.bmin),bounds,seed=seed,popsize=args.popsize,maxiter=args.maxiter,tol=1e-10,polish=True)
        print(seed,-opt.fun,opt.x,flush=True)
