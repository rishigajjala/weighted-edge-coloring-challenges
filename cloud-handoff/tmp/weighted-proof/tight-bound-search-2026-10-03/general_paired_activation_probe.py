"""Numerical falsification of 2/3 paired-vertex activation recourse.

General loopless fluid graphs; divisible fractional matching recourse, not
integer matchings. Random finite inputs only, never a proof.
"""
import itertools
import json
from pathlib import Path
import random
import time

import numpy as np
from scipy.optimize import linprog

rng = random.Random(2603100700)
started = time.time()
least = 100.
records = []
for trial in range(5000):
    groups = rng.choice([2, 3, 3, 4, 4, 5])
    n = 2 * groups
    pool = list(itertools.combinations(range(n), 2))
    edges = rng.sample(pool, rng.randint(1, min(len(pool), 2*n)))
    q = np.array([rng.choice([1., 1., 1., 2., 3., 5., 8.]) for _ in edges])
    D = np.array([rng.choice([.05, .1, 1/3, .5, 2/3, .8, 1., rng.random()])
                  for _ in range(groups)])
    inc = np.zeros((n, len(edges)))
    for i, (u, v) in enumerate(edges):
        inc[u, i] = inc[v, i] = 1.
    base = linprog(-q, A_ub=inc, b_ub=np.repeat(D, 2), bounds=(0, None))
    assert base.success
    p = 1/3 + 2*D/3
    expected = 0.
    values = []
    for bits in itertools.product((0, 1), repeat=groups):
        prob = np.prod(np.where(bits, p, 1-p))
        if prob < 1e-15:
            continue
        result = linprog(-q, A_ub=inc, b_ub=np.repeat(bits, 2), bounds=(0, None))
        assert result.success
        expected -= prob * result.fun
        values.append((bits, -float(result.fun)))
    ratio = expected/(-base.fun) if base.fun < -1e-12 else 1.
    least = min(least, ratio)
    if ratio < 2/3 - 1e-8:
        record = dict(trial=trial,groups=groups,edges=edges,q=q.tolist(),D=D.tolist(),
                      y=base.x.tolist(),base=-float(base.fun),expected=expected,
                      ratio=ratio,state_values=values)
        records.append(record)
        Path(__file__).with_suffix('.json').write_text(json.dumps(records,indent=2))
        print('COUNTEREXAMPLE CANDIDATE',json.dumps(record),flush=True)
        break
    if (trial+1)%200==0:
        print('Progress',trial+1,'least ratio',least,'elapsed',time.time()-started,flush=True)
else:
    print('Completed random probe; no proof implied.',least,flush=True)
