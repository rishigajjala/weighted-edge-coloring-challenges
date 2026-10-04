"""Numerical falsification only: exact activation sums, continuous optimizer.

No finite search over real parameters proves the proposed inequality.
The target edge joins two centers with independent competitor stars.
"""
import itertools
import json
from pathlib import Path
import time

import numpy as np
from scipy.optimize import differential_evolution


def shares(sticks):
    remaining = 1.0
    result = []
    for s in sticks:
        result.append(s * remaining)
        remaining *= 1 - s
    result.append(remaining)
    return np.array(result)


def make_problem(m, n, coefficient):
    bits_u = np.array(list(itertools.product((0, 1), repeat=m)))
    bits_v = np.array(list(itertools.product((0, 1), repeat=n)))

    def unpack(par):
        a = par[0]
        du_cap = a + (1 - a) * par[1]
        dv_cap = a + (1 - a) * par[2]
        du = (du_cap - a) * par[3]
        dv = (dv_cap - a) * par[4]
        off = 5
        ys = du * shares(par[off:off + m - 1])
        off += m - 1
        zs = dv * shares(par[off:off + n - 1])
        off += n - 1
        py = .25 + .75 * (ys + (1 - ys) * par[off:off + m])
        off += m
        pz = .25 + .75 * (zs + (1 - zs) * par[off:off + n])
        pu, pv = .25 + .75 * du_cap, .25 + .75 * dv_cap
        return a, du_cap, dv_cap, ys, zs, pu, pv, py, pz

    def objective(par):
        a, _, _, ys, zs, pu, pv, py, pz = unpack(par)
        factor = min(coefficient / (pu * pv), 12.)
        self_load = factor * a
        tentative_u = np.minimum(coefficient * ys / (pu * py), 12 * ys)
        tentative_v = np.minimum(coefficient * zs / (pv * pz), 12 * zs)
        loads_u = self_load + bits_u @ tentative_u
        loads_v = self_load + bits_v @ tentative_v
        probs_u = np.prod(np.where(bits_u, py, 1 - py), axis=1)
        probs_v = np.prod(np.where(bits_v, pz, 1 - pz), axis=1)
        denominator = np.maximum(1., np.maximum(loads_u[:, None], loads_v[None, :]))
        return factor * pu * pv * np.sum(probs_u[:, None] * probs_v[None, :] / denominator)

    return objective, unpack, 3 + 2 * (m + n)


if __name__ == '__main__':
    records = []
    started = time.time()
    for coefficient in [4 / 3, 2., 3.]:
        for m, n in [(1, 1), (1, 3), (2, 2), (2, 4), (3, 4), (4, 4)]:
            objective, unpack, dim = make_problem(m, n, coefficient)
            for seed in [37, 1903, 2627]:
                result = differential_evolution(
                    objective, [(0., 1.)] * dim, popsize=9, maxiter=1200,
                    tol=1e-10, atol=1e-12, polish=True, seed=seed,
                    updating='immediate', workers=1,
                )
                a, du, dv, ys, zs, pu, pv, py, pz = unpack(result.x)
                record = dict(K=coefficient, m=m, n=n, seed=seed,
                              ratio=float(result.fun), a=float(a), D=[float(du),float(dv)],
                              ys=ys.tolist(),zs=zs.tolist(),
                              p=[float(pu),float(pv)],py=py.tolist(),pz=pz.tolist(),
                              parameters=result.x.tolist(),evaluations=int(result.nfev),
                              elapsed=time.time()-started)
                records.append(record)
                print(json.dumps(record), flush=True)
                Path(__file__).with_suffix('.json').write_text(json.dumps(records, indent=2))
                if result.fun < .75 - 1e-8:
                    print('NUMERICAL COUNTEREXAMPLE CANDIDATE; NEED EXACT AUDIT', flush=True)
                    raise SystemExit(0)
    print('COMPLETED numerical search; no proof implied.', flush=True)
