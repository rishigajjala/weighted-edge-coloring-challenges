"""Test sequential counterquantiles for private pairs in a fluid star.

This is a falsification experiment, not an upper-bound proof.
"""
import json
from pathlib import Path
import numpy as np

HERE = Path(__file__).resolve().parent
rng = np.random.default_rng(20261003)


def law_with_mean(mean, cap):
    low = rng.uniform(0, mean)
    high = rng.uniform(mean, cap)
    if rng.random() < .25:
        low = 0.
    if rng.random() < .25:
        high = cap
    p = (mean-low)/(high-low)
    return [(float(low), float(1-p)), (float(high), float(p))]


def independent_sum(a, b):
    return sorted((x+y, p*q) for x,p in a for y,q in b)


def counter_sum(a, b):
    a = sorted(a)
    b = sorted(b, reverse=True)
    out = []
    i = j = 0
    pa, pb = a[0][1], b[0][1]
    while i < len(a) and j < len(b):
        p = min(pa, pb)
        out.append((a[i][0] + b[j][0], p))
        pa -= p
        pb -= p
        if pa < 1e-13:
            i += 1
            if i < len(a):
                pa = a[i][1]
        if pb < 1e-13:
            j += 1
            if j < len(b):
                pb = b[j][1]
    assert abs(sum(p for _,p in out)-1) < 1e-9
    return sorted(out)


best = -1
for trial in range(20000):
    n = int(rng.integers(0, 6))
    m = int(rng.integers(1, 6))
    r = rng.uniform(.1, 1)
    hub = law_with_mean(r, 1)
    if rng.random() < .25:
        r = 1.
        hub = [(1., 1.)]
    means = rng.dirichlet(np.full(n+m, .5)) * r * rng.uniform(.8, 1)
    shared = [law_with_mean(float(t), 1) for t in means[:n]]
    private = [law_with_mean(float(t), 2) for t in means[n:]]
    d = [(-x,p) for x,p in hub]
    for z in shared:
        d = independent_sum(d,z)
    for z in private:
        d = counter_sum(d,z)
    loss = sum(max(x,0)*p for x,p in d)
    if loss > best:
        best = loss
        witness = dict(trial=trial, loss=loss, hub=hub, shared=shared,
                       private=private, final_law=d)
    if loss > .5+1e-9:
        print('COUNTEREXAMPLE', json.dumps(witness), flush=True)
        break
else:
    print('NO COUNTEREXAMPLE in 20000 trials; maximum', best, flush=True)
(HERE/'primary_private_star_coupling.json').write_text(json.dumps(witness, indent=2))
