"""Nonexhaustive six-vertex probe of exact 2/3 local-to-global inclusion."""
import random
import sys
from pathlib import Path

import numpy as np

sys.path.insert(0,str(Path(__file__).resolve().parent.parent))
from exploration_heavy_fluid_polytope import local_opt,scaled_feasible


if __name__=='__main__':
    rng=random.Random(20261003)
    all6=[(u,v) for u in range(6) for v in range(u+1,6)]
    count=0
    for t in range(300):
        H=rng.sample(all6,rng.choice((5,6,7,8,9)))
        F=rng.sample(all6,rng.choice((6,8,10,12,15)))
        w=[rng.choice((.51,.55,.6,.7,.8,.9,.99,1.)) for _ in H]
        p=np.array([rng.uniform(.05,2) for _ in H])
        q=np.array([rng.uniform(.05,2) for _ in F])
        x,L=local_opt(6,H,F,w,p,q)
        ok,nm=scaled_feasible(6,H,F,w,x)
        count+=1
        if not ok:
            print('FAIL',dict(H=H,F=F,w=w,p=p.tolist(),q=q.tolist(),x=x.tolist(),L=L,matchings=nm),flush=True)
            break
    else:
        print('PASS',count,'nonexhaustive instances; not a theorem',flush=True)
