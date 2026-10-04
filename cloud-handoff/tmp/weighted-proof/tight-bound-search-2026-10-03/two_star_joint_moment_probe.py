"""Diagnostic only: does covariance zero plus second moments suffice?"""
import argparse
import numpy as np
from scipy.optimize import linprog
from two_star_moment_altlp_scan import moments


def solve(du, dv, y, points=71, quartic=False):
    pu, pv = (1+3*du)/4, (1+3*dv)/4
    if pu*pv < 1/9: return None
    b = (4/3)*y/(pu*pv)
    mu, vu = moments(du,y)
    mv, vv = moments(dv,y)
    gx = np.unique(np.r_[np.linspace(0,16/3,points),mu,max(0,1-b)])
    gy = np.unique(np.r_[np.linspace(0,16/3,points),mv,max(0,1-b)])
    x,z=np.meshgrid(gx,gy,indexing='ij'); x=x.ravel(); z=z.ravel()
    c=1/np.maximum(1,b+np.maximum(x,z))
    au,av=mu*mu+vu+1e-12,mv*mv+vv+1e-12
    ub=[x*x,z*z]; rhs=[au,av]
    eq=[np.ones(len(x)),x,z,x*z]; erhs=[1,mu,mv,mu*mv]
    if quartic:
        eq += [x*x*(z-mv),z*z*(x-mu)];erhs += [0,0]
        ub += [x*x*z*z-au*z*z,x*x*z*z-av*x*x,-x*x*z*z+au*z*z+av*x*x]
        rhs += [0,0,au*av]
    res=linprog(c,A_ub=np.array(ub),b_ub=rhs,A_eq=np.array(eq),b_eq=erhs,bounds=(0,None),method='highs')
    if not res.success:return None
    support=[(float(x[i]),float(z[i]),float(res.x[i])) for i in np.flatnonzero(res.x>1e-7)]
    return float(res.fun),support,res.eqlin.marginals.tolist(),res.ineqlin.marginals.tolist()


if __name__=='__main__':
    parser=argparse.ArgumentParser();parser.add_argument('--trials',type=int,default=100);parser.add_argument('--quartic',action='store_true');args=parser.parse_args()
    rng=np.random.default_rng(177)
    worst=(2,None)
    params=[(1,1,0),(1,.5,.1),(.5,.5,.1),(1,1,1/3),(1,1/3,1/3)]
    params += [(du,dv,min(du,dv)*rng.random()) for du,dv in rng.random((args.trials,2))]
    for pars in params:
        out=solve(*pars,quartic=args.quartic)
        if out is not None and out[0]<worst[0]:
            worst=(out[0],pars);print('worst',worst,'certificate',out[1:],flush=True)
    print('done',worst)
