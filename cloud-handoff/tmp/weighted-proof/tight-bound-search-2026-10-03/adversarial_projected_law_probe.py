"""Adversarial-law test for the mixed heavy/fluid repair conjecture.

Floating-point diagnostic only: no numerical result is a proof.
"""
import itertools
import json
from pathlib import Path
import random
import numpy as np
from scipy.optimize import linprog
from projected_matching_law_repair_probe import matchings


def trial(rng, number):
    n = rng.choice([5, 6, 7, 8])
    pairs = list(itertools.combinations(range(n), 2))
    H = rng.sample(pairs, rng.randint(n-1, min(len(pairs), n+5)))
    F = rng.sample(pairs, rng.randint(n-1, min(len(pairs), n+5)))
    w = np.array([rng.choice([.5001, .51, .55, .6, .7, .8, .9, 1]) for _ in H])
    p = np.array([rng.choice([0, 1, 2, 3, 4]) for _ in H+F])
    nh, nf = len(H), len(F)
    local = np.zeros((2*n, nh+nf))
    for i, (u,v) in enumerate(H):
        local[u,i] = local[v,i] = 1
        local[n+u,i] = local[n+v,i] = w[i]
    for j, (u,v) in enumerate(F):
        local[n+u,nh+j] = local[n+v,nh+j] = 1
    loc = linprog(-p, A_ub=local, b_ub=np.ones(2*n), bounds=(0,None))
    assert loc.success
    hi = [i for i in range(nh) if loc.x[i] > 1e-9]
    fi = [j for j in range(nf) if loc.x[nh+j] > 1e-9]
    x, y = loc.x[hi], loc.x[[nh+j for j in fi]]
    H, F, w = [H[i] for i in hi], [F[j] for j in fi], w[hi]
    nh, nf = len(H), len(F)
    if not nf: return False, None
    z = (2/3)*np.r_[x,y]
    ms = matchings(n, H+F)
    inc = np.zeros((nh+nf, len(ms)))
    for j, M in enumerate(ms): inc[M,j] = 1
    counts = inc[nh:].sum(axis=0)
    eq = np.vstack([np.ones(len(ms)), inc[:nh]])
    rhs = np.r_[1,z[:nh]]
    proj = linprog(-counts,A_eq=eq,b_eq=rhs,A_ub=inc[nh:],b_ub=z[nh:],bounds=(0,None))
    assert proj.success
    removed = z[nh:].sum()+proj.fun
    if removed < 1e-8: return False, None
    law_eq, law_rhs = np.vstack([eq,counts]), np.r_[rhs,-proj.fun]
    heavy_states = {tuple(e for e in M if e < nh) for M in ms}
    fluid_inc = np.zeros((n,nf))
    for j,(u,v) in enumerate(F): fluid_inc[u,j]=fluid_inc[v,j]=1
    for rep in range(5):
        q = np.ones(nf) if rep == 0 else np.array([rng.choice([0,1,2,3,4,8]) for _ in F])
        state_cost = {}
        for A in heavy_states:
            cap = np.ones(n)
            for e in A:
                for v in H[e]: cap[v] -= w[e]
            fluid = linprog(-q,A_ub=fluid_inc,b_ub=cap,bounds=(0,None))
            assert fluid.success
            state_cost[A] = -fluid.fun
        cost = np.array([state_cost[tuple(e for e in M if e<nh)] for M in ms])
        worst = linprog(cost,A_eq=law_eq,b_eq=law_rhs,A_ub=inc[nh:],b_ub=z[nh:],bounds=(0,None))
        assert worst.success
        target = q@z[nh:]
        if target-worst.fun > 1e-7:
            return True, dict(trial=number,n=n,H=H,F=F,w=w.tolist(),x=x.tolist(),y=y.tolist(),
                q=q.tolist(),removed=removed,target=target,recourse=worst.fun,
                gap=target-worst.fun,unit_law=[[M,float(v)] for M,v in zip(ms,worst.x) if v>1e-10],
                projected=(inc@worst.x).tolist())
    return True, None


if __name__ == '__main__':
    rng = random.Random(2026100341)
    tested = 0
    for i in range(1500):
        nontrivial, result = trial(rng,i)
        tested += nontrivial
        if result:
            Path(__file__).with_suffix('.json').write_text(json.dumps(result,indent=2))
            print(json.dumps(result),flush=True)
            break
        if i%100 == 99: print(f'{i+1} instances; {tested} nontrivial projections',flush=True)
    else:
        print(f'No counterexample; {tested} nontrivial projections in 1500 instances.',flush=True)
