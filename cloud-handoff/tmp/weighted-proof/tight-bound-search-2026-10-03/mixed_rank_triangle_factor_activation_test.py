"""Targeted factor-inequality test for (.4,.3) mixed spoke bundles.

Left port: two .4 spokes, .7 blocker excludes all.
Right port: three .3 spokes, .7 blocker permits one.
Hub patterns: (0,3),(1,2),(2,0).
"""
import json
import sys
from scipy.optimize import differential_evolution, linprog


def local(x,z,q,u,v):
    # vars p,l,r
    A=[[1,.5,0],[1,0,1/3],[1,0,0],[0,1,1],[0,2,1]]
    b=[1-x,1-2*z/3,1-z,3,4]
    res=linprog([-q,-u,-v],A_ub=A,b_ub=b,bounds=[(0,None)]*3,method='highs')
    if not res.success: raise RuntimeError(res.message)
    return -res.fun,res.x


def expected(x,z,q,u,v):
    px,pz=2*x/3,2*z/3
    f00=max(q,2*u,u+2*v,3*v)
    f10=3*v
    f01=max(2*u,u+v,v)
    f11=v
    return ((1-px)*(1-pz)*f00+px*(1-pz)*f10+
            (1-px)*pz*f01+px*pz*f11),(f00,f10,f01,f11)


def ratio(a):
    x,z,q,u,v=a
    g,_=local(x,z,q,u,v)
    e,_=expected(x,z,q,u,v)
    return g/e if e>1e-10 else 0


if __name__=='__main__':
    trials=int(sys.argv[1]) if len(sys.argv)>1 else 3
    for seed in range(trials):
        res=differential_evolution(lambda a:-ratio(a),[(0,1)]*5,
            seed=seed,maxiter=350,popsize=12,tol=1e-9,polish=True)
        x,z,q,u,v=res.x
        g,pattern=local(x,z,q,u,v)
        e,conditional=expected(x,z,q,u,v)
        print(json.dumps(dict(seed=seed,ratio=g/e,params=res.x.tolist(),
            local=g,expected=e,local_pattern=pattern.tolist(),
            conditional=conditional)),flush=True)
