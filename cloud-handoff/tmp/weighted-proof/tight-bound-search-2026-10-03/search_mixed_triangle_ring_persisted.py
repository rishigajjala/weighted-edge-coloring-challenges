"""Finite-grid diagnostic with exhaustive, integer global-pattern pricing.

All source instances have equal capacity 100. This is not an upper bound
for arbitrary graphs or arbitrary real profit vectors. No solver incumbent
is called a lower witness until priced against every maximal configuration.
"""
import argparse
import itertools
import json
from pathlib import Path
import sys
import time

import numpy as np
import gurobipy as gp
from gurobipy import GRB

HERE = Path(__file__).resolve().parent
sys.path.insert(0, str(HERE.parent))
import search_three_triangles_mixed_heavy_ring as template

c = template.core
EDGES = c.E
PATTERNS = HERE / "mixed_triangle_ring_maximal_patterns.npy"
CHECKPOINT = HERE / "mixed_triangle_ring_cuts.json"


def enumerate_patterns():
    """Enumerate each maximal integer feasible vector exactly once.

    There is at most one heavy edge per triangle. Conditional on those
    choices, enumerate each medium bundle and reject over-capacity rows.
    At each leaf, discard vectors admitting any single-type augmentation.
    Every nonmaximal vector is dominated by a maximal one.
    """
    pairs = []
    for e in range(18, len(EDGES)):
        uv = tuple(sorted(EDGES[e][:2]))
        if uv not in pairs:
            pairs.append(uv)
    groups = []
    for uv in pairs:
        idx = [e for e in range(18, len(EDGES))
               if tuple(sorted(EDGES[e][:2])) == uv]
        options = [(sum(a * EDGES[e][2] for a, e in zip(z, idx)), z)
                   for z in itertools.product(*[range(101 // EDGES[e][2] + 1)
                                                  for e in idx])]
        options = [(w, z) for w, z in options if w <= 100]
        groups.append((uv, idx, options))
    out = []
    z = [0] * len(EDGES)
    load = [0] * 9

    def visit(k):
        if k == len(groups):
            if any(load[u] + w <= 100 and load[v] + w <= 100
                   for u, v, w in EDGES):
                return
            out.append(tuple(z))
            return
        (u, v), idx, opts = groups[k]
        room = min(100 - load[u], 100 - load[v])
        for weight, counts in opts:
            if weight > room:
                continue
            load[u] += weight
            load[v] += weight
            for e, n in zip(idx, counts):
                z[e] = n
            visit(k + 1)
            load[u] -= weight
            load[v] -= weight
        for e in idx:
            z[e] = 0

    for choices in itertools.product(*[[-1] + list(range(6*t, 6*t+6))
                                       for t in range(3)]):
        for e in choices:
            if e >= 0:
                u, v, w = EDGES[e]
                load[u] += w
                load[v] += w
                z[e] = 1
        visit(0)
        for e in choices:
            if e >= 0:
                u, v, w = EDGES[e]
                load[u] -= w
                load[v] -= w
                z[e] = 0
    result = np.array(out, dtype=np.int16)
    assert result.shape[1] == 30
    assert len({tuple(row) for row in result.tolist()}) == len(result)
    for v in range(9):
        weights = np.array([w if v in (u, t) else 0 for u, t, w in EDGES])
        assert np.all(result @ weights <= 100)
    np.save(PATTERNS, result)
    print(json.dumps({"event": "enumeration", "maximal_patterns": len(result)}), flush=True)
    return result


def search(Q, seconds, unrestricted_cap=False):
    start = time.monotonic()
    P = np.load(PATTERNS) if PATTERNS.exists() else enumerate_patterns()

    def price(q):
        values = P @ np.array(q, dtype=np.int64)
        k = int(np.argmax(values))
        return int(values[k]), tuple(int(a) for a in P[k])

    # Independently compare the exhaustive oracle with the original integer
    # optimization oracle, including many tied and zero-price directions.
    rng = np.random.default_rng(1032026)
    for j in range(30):
        qv = rng.integers(0, Q + 1, size=30).tolist()
        a, _ = price(qv)
        b, _ = c.price(qv)
        assert a == b, (j, a, b)
    print(json.dumps({"event": "oracle_check", "patterns": len(P),
                      "independent_pricings": 30}), flush=True)

    m = gp.Model("mixed-triangle-ring")
    m.Params.OutputFlag = 0
    m.Params.Threads = 3
    m.Params.MIPGap = 0
    m.Params.FeasibilityTol = 1e-8
    m.Params.IntFeasTol = 1e-8
    lam = [[m.addVar(lb=0) for _ in states] for _, states in c.LOCAL]
    x = [m.addVar(lb=0, ub=100 // w) for _, _, w in EDGES]
    q = [m.addVar(vtype=GRB.INTEGER, lb=0, ub=Q) for _ in EDGES]
    cap_upper = int(np.max(P.sum(axis=1))) * Q if unrestricted_cap else Q
    K = m.addVar(vtype=GRB.INTEGER, lb=1, ub=cap_upper)
    bits = Q.bit_length()
    b = [[m.addVar(vtype=GRB.BINARY) for _ in range(bits)] for _ in EDGES]
    t = [[m.addVar(lb=0) for _ in range(bits)] for _ in EDGES]
    for v, (idx, states) in enumerate(c.LOCAL):
        m.addConstr(gp.quicksum(lam[v]) == 1)
        for k, e in enumerate(idx):
            m.addConstr(x[e] == gp.quicksum(states[j][k] * lam[v][j]
                                           for j in range(len(states))))
    for e in range(0, 18, 2):
        m.addConstr(x[e] + x[e+1] == .5)
    for e, (_, _, w) in enumerate(EDGES):
        U = 100 // w
        m.addConstr(q[e] == gp.quicksum((1 << h) * b[e][h] for h in range(bits)))
        for h in range(bits):
            m.addConstr(t[e][h] <= U * b[e][h])
            m.addConstr(t[e][h] <= x[e])
            m.addConstr(t[e][h] >= x[e] - U * (1 - b[e][h]))
    raw = gp.quicksum((1 << h) * t[e][h] for e in range(30) for h in range(bits))
    m.setObjective((raw - 1.5*K)/Q, GRB.MAXIMIZE)
    cuts = set()
    if CHECKPOINT.exists():
        cuts.update(tuple(z) for z in json.loads(CHECKPOINT.read_text())["cuts"])
    # Seed global facets with randomly exposed maximal configurations,
    # adding pure-heavy and pure-medium objectives as well.
    for _ in range(300):
        profits = rng.integers(0, Q+1, size=30).tolist()
        _, z = price(profits)
        cuts.add(z)
    for e in range(30):
        profits = [0]*30
        profits[e] = 1
        _, z = price(profits)
        cuts.add(z)
    for z in sorted(cuts):
        m.addConstr(gp.quicksum(z[e]*q[e] for e in range(30)) <= K)
    m.update()
    print(json.dumps({"event": "start", "Q": Q, "cap_upper": cap_upper,
                      "unrestricted_cap": unrestricted_cap, "variables": m.NumVars,
                      "constraints": m.NumConstrs, "seed_cuts": len(cuts)}), flush=True)
    # Cut in a lazy callback to keep the branch-and-bound tree. New cuts
    # are checkpointed so future runs need not rediscover them.
    m.Params.LazyConstraints = 1
    state = {"best_priced_ratio": 1.5, "callbacks": 0, "cuts_added": 0,
             "unrestricted_cap": unrestricted_cap}
    base_constraints = m.NumConstrs

    def save():
        CHECKPOINT.write_text(json.dumps({"edges": EDGES, "cuts": sorted(cuts),
                                          "state": state}, indent=2))

    last_report = [time.monotonic()]

    def callback(model, where):
        if where == GRB.Callback.MIP and time.monotonic()-last_report[0] >= 30:
            last_report[0] = time.monotonic()
            state["elapsed"] = time.monotonic()-start
            state["master_upper"] = model.cbGet(GRB.Callback.MIP_OBJBND)
            state["master_incumbent"] = model.cbGet(GRB.Callback.MIP_OBJBST)
            save()
            print(json.dumps({"event": "heartbeat", "elapsed": state["elapsed"],
                              "master_upper": state["master_upper"],
                              "master_incumbent": state["master_incumbent"],
                              "cuts_added": state["cuts_added"]}), flush=True)
        if where != GRB.Callback.MIPSOL:
            return
        state["callbacks"] += 1
        qv = tuple(int(round(v)) for v in model.cbGetSolution(q))
        cap = int(round(model.cbGetSolution(K)))
        xv = model.cbGetSolution(x)
        actual, z = price(qv)
        local = sum(a*y for a,y in zip(qv,xv))
        ratio = local / actual if actual else 0
        if ratio > state["best_priced_ratio"] + 1e-7:
            state.update(best_priced_ratio=ratio, best_prices=qv,
                         best_means=xv, best_pattern=z,
                         best_local_laws=[model.cbGetSolution(l) for l in lam])
            print(json.dumps({"event": "priced_improvement", **state}), flush=True)
        if actual > cap:
            model.cbLazy(gp.quicksum(z[e]*q[e] for e in range(30)) <= K)
            if z not in cuts:
                cuts.add(z)
                state["cuts_added"] += 1
            if base_constraints + state["cuts_added"] > 1850:
                state["cut_limit"] = True
                model.terminate()
        if state["callbacks"] % 25 == 0:
            state["elapsed"] = time.monotonic()-start
            save()
            print(json.dumps({"event": "progress", **{k:v for k,v in state.items()
                                                       if not k.startswith('best_')},
                              "best_priced_ratio": state["best_priced_ratio"]}), flush=True)

    m.Params.TimeLimit = max(1, seconds-(time.monotonic()-start))
    m.optimize(callback)
    state.update(finished=True, solver_status=m.Status, elapsed=time.monotonic()-start,
                 grid=Q, maximal_patterns=len(P), master_upper=m.ObjBound,
                 incumbent=m.ObjVal if m.SolCount else None)
    if m.SolCount:
        qv = tuple(int(round(v.X)) for v in q)
        actual, z = price(qv)
        cap = int(round(K.X))
        state.update(final_prices=qv, final_means=[v.X for v in x],
                     final_cap=cap, final_global=actual,
                     final_fully_priced=actual <= cap)
    save()
    tag = "cube" if unrestricted_cap else "grid"
    (HERE / f"mixed_triangle_ring_{tag}{Q}_result.json").write_text(json.dumps(state, indent=2))
    print(json.dumps({"event": "terminal", **state}), flush=True)


if __name__ == "__main__":
    parser = argparse.ArgumentParser()
    parser.add_argument("--grid", type=int, default=8)
    parser.add_argument("--seconds", type=int, default=600)
    parser.add_argument("--unrestricted-cap", action="store_true")
    args = parser.parse_args()
    search(args.grid, args.seconds, args.unrestricted_cap)
