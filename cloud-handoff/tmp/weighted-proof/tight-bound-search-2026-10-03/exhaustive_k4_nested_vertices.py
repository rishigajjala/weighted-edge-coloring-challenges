"""Enumerate all local vertices for a fixed K4 heavy-weight vector.

Every pair has one heavy type and one divisible fluid type. Compare the
vertices with the exact 91-generator nested-matching polytope. Linear
algebra and LPs are floating point; a failed candidate must be checked
over rationals before it becomes a counterexample.
"""
import itertools
import json
from pathlib import Path
import time

import numpy as np
from scipy.optimize import linprog

PAIRS = list(itertools.combinations(range(4), 2))
INC = np.array([[int(v in e) for e in PAIRS] for v in range(4)], dtype=float)
HERE = Path(__file__).resolve().parent


def generators(w):
    fluid = []
    for e, uv in enumerate(PAIRS):
        for f in range(e+1, 6):
            if not set(uv).intersection(PAIRS[f]):
                z = np.zeros(6)
                z[[e,f]] = 1
                fluid.append(z)
    for tri in itertools.combinations(range(4), 3):
        fluid.append(np.array([.5 if set(e).issubset(tri) else 0 for e in PAIRS]))
    assert len(fluid) == 7
    out = [np.r_[np.zeros(6), f] for f in fluid]
    for e, uv in enumerate(PAIRS):
        opp = next(f for f, ab in enumerate(PAIRS) if not set(uv).intersection(ab))
        h = np.eye(6)[e]
        for f in fluid:
            out.append(np.r_[h, w[e]*np.eye(6)[opp]+(1-w[e])*f])
    for e, uv in enumerate(PAIRS):
        for f in range(e+1, 6):
            if set(uv).intersection(PAIRS[f]):
                continue
            h = np.eye(6)[e]+np.eye(6)[f]
            for t in [w[e]+w[f]-1, min(w[e],w[f])]:
                for z in fluid:
                    y = ((w[e]-t)*np.eye(6)[f]+(w[f]-t)*np.eye(6)[e]
                         +(1-w[e]-w[f]+t)*z)
                    out.append(np.r_[h,y])
    assert len(out) == 91
    return np.array(out)


def local_vertices(w):
    A = np.block([[INC, np.zeros((4,6))], [INC*w, INC]])
    found = {tuple([0.0]*12): np.zeros(12)}
    bases = 0
    for k in range(1, 9):
        supports = np.array(list(itertools.combinations(range(12), k)))
        for rows in itertools.combinations(range(8), k):
            matrices = A[list(rows)][:, supports].transpose(1,0,2)
            nonsingular = np.abs(np.linalg.det(matrices)) > 1e-10
            if not np.any(nonsingular):
                continue
            matrices = matrices[nonsingular]
            cols = supports[nonsingular]
            sols = np.linalg.solve(matrices, np.ones((len(matrices),k,1)))[:,:,0]
            positive = np.all(sols > 1e-8, axis=1)
            sols, cols = sols[positive], cols[positive]
            if not len(sols):
                continue
            full = np.zeros((len(sols),12))
            full[np.arange(len(sols))[:,None],cols] = sols
            feasible = np.all(full @ A.T <= 1+1e-8, axis=1)
            bases += int(np.sum(feasible))
            for x in full[feasible]:
                found[tuple(np.round(x,9))] = x
    return np.array(list(found.values())), bases


def run():
    start = time.monotonic()
    rng = np.random.default_rng(3102026)
    weights = [[.6]*6,[.75]*6,[.9]*6,[1.]*6,
               [.55,.65,.75,.85,.95,1.],
               [.51,.52,.6,.7,.8,.99]]
    # Distinct arrangements matter: random mixed assignments include both
    # opposite- and incident-pair type interactions.
    weights += [rng.choice([.55,.6,.7,.8,.9,1.],6).tolist() for _ in range(24)]
    results = {"finished":False,"seed":3102026,"cases":[],"counterexample":None}
    for w in weights:
        w = np.array(w)
        vertices, bases = local_vertices(w)
        P = generators(w)
        worst = 0
        worst_x = None
        min_positive_slack = 100
        tight = 0
        for x in vertices:
            lp = linprog(np.ones(len(P)), A_ub=-P.T, b_ub=-x,
                         bounds=(0,None), method="highs")
            assert lp.success, lp.message
            assert np.max(x-P.T @ lp.x) < 1e-7
            if lp.fun > worst:
                worst, worst_x = float(lp.fun), x.tolist()
            if abs(lp.fun-1.5) < 1e-7:
                tight += 1
            elif lp.fun < 1.5:
                min_positive_slack = min(min_positive_slack,1.5-lp.fun)
            if lp.fun > 1.5+1e-7:
                results["counterexample"] = {"weights":w.tolist(),"means":x.tolist(),
                    "gauge":float(lp.fun),"dual":(-lp.ineqlin.marginals).tolist()}
                break
        item = {"weights":w.tolist(),"vertices":len(vertices),"feasible_bases":bases,
                "max_gauge":worst,"worst_vertex":worst_x,"tight_vertices":tight,
                "next_slack":min_positive_slack,"elapsed":time.monotonic()-start}
        results["cases"].append(item)
        (HERE / "exhaustive_k4_nested_vertices.json").write_text(json.dumps(results,indent=2))
        print(json.dumps(item),flush=True)
        if results["counterexample"]:
            print(json.dumps(results["counterexample"]),flush=True)
            break
    results["finished"] = True
    results["elapsed"] = time.monotonic()-start
    (HERE / "exhaustive_k4_nested_vertices.json").write_text(json.dumps(results,indent=2))
    print(json.dumps({"finished":True,"elapsed":results["elapsed"],
                      "counterexample":results["counterexample"]}),flush=True)


if __name__ == "__main__":
    run()
