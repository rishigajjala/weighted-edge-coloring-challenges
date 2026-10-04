"""K=3 expected-max search after convex-order reduction to minimal leaf p."""

import argparse
from itertools import product
import numpy as np
from scipy.optimize import differential_evolution


def gap(x,m,n):
    y=x[0];a=np.array(x[1:1+m]);b=np.array(x[1+m:1+m+n])
    du=y+a.sum();dv=y+b.sum()
    if du>1 or dv>1:return 2+max(du-1,dv-1)
    pu,pv=(1+3*du)/4,(1+3*dv)/4
    if pu*pv<.25:return 2+(.25-pu*pv)
    ru=(1+3*a)/4;rv=(1+3*b)/4
    xu=a/(pu*ru);xv=b/(pv*rv);be=y/(pu*pv)
    bitsu=np.array(list(product((0.,1.),repeat=m)))
    bitsv=np.array(list(product((0.,1.),repeat=n)))
    probu=np.prod(np.where(bitsu>0,ru,1-ru),axis=1)
    probv=np.prod(np.where(bitsv>0,rv,1-rv),axis=1)
    lu=bitsu@xu;lv=bitsv@xv
    den=np.maximum.reduce([np.full((len(lu),len(lv)),1/3),
                           be+lu[:,None]+np.zeros((1,len(lv))),
                           be+lv[None,:]+np.zeros((len(lu),1))])
    return 4/3-(probu[:,None]*probv[None,:]*den).sum()


if __name__=='__main__':
    pa=argparse.ArgumentParser();pa.add_argument('--u',type=int,default=4)
    pa.add_argument('--v',type=int,default=4)
    pa.add_argument('--maxiter',type=int,default=2500)
    args=pa.parse_args();m=args.u;n=args.v
    opt=differential_evolution(lambda x:gap(x,m,n),[(1e-9,1)]+[(0,1)]*(m+n),
                               seed=9396,popsize=18,maxiter=args.maxiter,
                               tol=1e-10,polish=True)
    print('min gap',opt.fun,'m,n',m,n,'x',opt.x,'evals',opt.nfev)
