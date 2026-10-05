import itertools
import math
import random

import numpy as np
from scipy.optimize import linprog


def recourse(edges, caps, profits, active, n):
    inc = np.zeros((n, len(edges)))
    for j, (u, v) in enumerate(edges):
        inc[u, j] = inc[v, j] = 1
    bound = [(0, caps[j] if active[edges[j][0]] and active[edges[j][1]] else 0) for j in range(len(edges))]
    result = linprog(-np.array(profits), A_ub=inc, b_ub=np.ones(n), bounds=bound, method="highs")
    assert result.success
    return -result.fun


def probe(seed=20261004, trials=2500):
    rng = random.Random(seed)
    best = (float("inf"), None)
    for t in range(trials):
        k = rng.choice([2, 3, 4])
        n = 2*k
        pairs = [(2*i, 2*i+1) for i in range(k)]
        candidates = [(u, v) for u in range(n) for v in range(u+1, n)]
        edges = [e for e in candidates if rng.random() < rng.uniform(.23, .65)]
        if not edges:
            continue
        raw = np.array([10**rng.uniform(-2, 0) for _ in edges])
        loads = [sum(raw[j] for j,e in enumerate(edges) if v in e) for v in range(n)]
        allowed = [rng.uniform(.05,1) for _ in pairs]
        scale = min(1, *(allowed[v//2]/loads[v] for v in range(n) if loads[v]>0))
        y = scale*raw
        if rng.random() < .6:
            allowed = [max(sum(y[j] for j,e in enumerate(edges) if v in e) for v in pair) for pair in pairs]
        p = [(1+2*d)/3 for d in allowed]
        caps = [12*float(z)*rng.choice([1, 1, 1, 2, 5]) for z in y]
        profits = [10**rng.uniform(-1, 1) for _ in edges]
        target = sum(q*z for q,z in zip(profits,y))
        if target < 1e-8:
            continue
        values = []
        for mask in range(1<<k):
            active = [bool(mask & (1<<i)) for i in range(k) for _ in range(2)]
            values.append(recourse(edges, caps, profits, active, n))
        independent = sum(values[mask] * math.prod(p[i] if mask & (1<<i) else 1-p[i] for i in range(k)) for mask in range(1<<k))
        comono = 0.0
        thresholds = sorted(set([0.0, 1.0] + p))
        for a,b in zip(thresholds, thresholds[1:]):
            mid = (a+b)/2
            mask = sum(1<<i for i in range(k) if mid <= p[i])
            comono += (b-a)*values[mask]
        ratio = (.75*independent+.25*comono)/target
        if ratio < best[0]:
            best = (ratio, dict(trial=t,pairs=pairs,edges=edges,y=list(map(float,y)),D=allowed,C=caps,q=profits,independent=independent/target,comono=comono/target))
            print(best, flush=True)
    return best


if __name__ == "__main__":
    probe()
