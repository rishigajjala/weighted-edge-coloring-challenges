"""Bounded joint demand/profit MILP for two disjoint triangles with K3,3 ports.

Research diagnostic only. Unit capacity is 20; every type is repeatable.
The local side uses complete integer-star pattern lists. Global pricing is
an exact six-capacity integer program and cuts all violated global patterns.
An incumbent is a genuine lower witness only after exact repricing.
"""
import itertools
import json
import sys
import time

import gurobipy as gp
from gurobipy import GRB

CAP = 20
H = [(0, 1, 11), (1, 2, 13), (0, 2, 16),
     (3, 4, 13), (4, 5, 16), (3, 5, 11)]
W = [[8, 6, 4], [4, 8, 6], [6, 4, 8]]
E = H + [(i, j + 3, W[i][j]) for i in range(3) for j in range(3)]
if "--parallel-small" in sys.argv:
    E += [(i, i + 3, 3) for i in range(3)]
N = len(E)
NV = 1 + max(max(u,v) for u,v,_ in E)
NH = len(H)


def local_patterns(v):
    idx = [e for e, (u, z, _) in enumerate(E) if v in (u, z)]
    weights = [E[e][2] for e in idx]
    return idx, [a for a in itertools.product(*[range(CAP // w + 1)
                                                 for w in weights])
                 if sum(k * w for k, w in zip(a, weights)) <= CAP]


LOCAL = [local_patterns(v) for v in range(NV)]


def price(q):
    m = gp.Model("global-pricing")
    m.Params.OutputFlag = 0
    z = [m.addVar(vtype=GRB.INTEGER, lb=0, ub=CAP // w)
         for _, _, w in E]
    for v in range(NV):
        m.addConstr(gp.quicksum(E[e][2] * z[e] for e in range(N)
                                if v in E[e][:2]) <= CAP)
    m.setObjective(gp.quicksum(q[e] * z[e] for e in range(N)), GRB.MAXIMIZE)
    m.optimize()
    assert m.Status == GRB.OPTIMAL
    return int(round(m.ObjVal)), tuple(int(round(a.X)) for a in z)


def search(Q=8, seconds=280, min_cross_price=0, gap_objective=True,
           fixed_heavy_mean=None, fixed_heavy_pair_sum=None):
    start = time.time()
    m = gp.Model("joint-two-triangle-K33")
    m.Params.OutputFlag = 0
    m.Params.MIPGap = 1e-5
    lam = [[m.addVar(lb=0) for _ in states] for _, states in LOCAL]
    x = [m.addVar(lb=0, ub=CAP // w) for _, _, w in E]
    q = [m.addVar(vtype=GRB.INTEGER, lb=0, ub=Q) for _ in E]
    K = m.addVar(vtype=GRB.INTEGER, lb=1, ub=Q) if gap_objective else None
    bits = Q.bit_length()
    b = [[m.addVar(vtype=GRB.BINARY) for _ in range(bits)] for _ in E]
    t = [[m.addVar(lb=0) for _ in range(bits)] for _ in E]
    for v, (idx, states) in enumerate(LOCAL):
        m.addConstr(gp.quicksum(lam[v]) == 1)
        for k, e in enumerate(idx):
            m.addConstr(x[e] == gp.quicksum(states[j][k] * lam[v][j]
                                           for j in range(len(states))))
    if fixed_heavy_mean is not None:
        for e in range(NH):
            m.addConstr(x[e] == fixed_heavy_mean)
    if fixed_heavy_pair_sum is not None:
        assert NH % 2 == 0
        for e in range(0, NH, 2):
            m.addConstr(x[e] + x[e+1] == fixed_heavy_pair_sum)
    for e, (_, _, w) in enumerate(E):
        U = CAP // w
        m.addConstr(q[e] == gp.quicksum((1 << h) * b[e][h]
                                       for h in range(bits)))
        for h in range(bits):
            m.addConstr(t[e][h] <= U * b[e][h])
            m.addConstr(t[e][h] <= x[e])
            m.addConstr(t[e][h] >= x[e] - U * (1 - b[e][h]))
    if min_cross_price:
        m.addConstr(gp.quicksum(q[e] for e in range(NH, N)) >= min_cross_price)
    raw_profit = gp.quicksum((1 << h) * t[e][h]
                             for e in range(N) for h in range(bits))
    m.setObjective((raw_profit - 1.5 * K if gap_objective else raw_profit) / Q,
                   GRB.MAXIMIZE)
    # Start with obvious one-color cuts, then separate all other patterns.
    cuts = set()
    for e, (_, _, w) in enumerate(E):
        z = tuple(CAP // w if j == e else 0 for j in range(N))
        cuts.add(z)
        m.addConstr(gp.quicksum(z[j] * q[j] for j in range(N)) <=
                    (K if gap_objective else Q))
    out = {"Q": Q, "min_cross_price_numerator": min_cross_price,
           "fixed_heavy_mean": fixed_heavy_mean,
           "fixed_heavy_pair_sum": fixed_heavy_pair_sum,
           "gap_objective": gap_objective,
           "weights": [w for _, _, w in E],
           "edges": [a[:2] for a in E], "local_patterns":
           [len(s) for _, s in LOCAL]}
    iteration = 0
    while time.time() - start < seconds:
        iteration += 1
        m.Params.TimeLimit = max(1, seconds - (time.time() - start))
        m.optimize()
        if m.SolCount == 0:
            out.update(status="no_incumbent", iterations=iteration)
            break
        qv = tuple(int(round(a.X)) for a in q)
        cap = int(round(K.X)) if gap_objective else Q
        c, z = price(qv)
        xv = [a.X for a in x]
        L = sum(qv[e] * xv[e] for e in range(N)) / Q
        ratio = L * Q / c if c else 0
        out.update(iterations=iteration, elapsed=time.time() - start,
                   incumbent_objective=m.ObjVal, local_value=L,
                   chosen_cap=cap / Q, exact_global_price=c / Q,
                   exact_ratio=ratio, profit_numerators=qv,
                   mean_counts=xv, pricing_pattern=z, cuts=len(cuts),
                   solver_status=m.Status)
        print(json.dumps(out), flush=True)
        if c <= cap:
            out["status"] = ("fully_priced_grid_optimum" if m.Status == GRB.OPTIMAL
                             else "repriced_feasible_incumbent_only")
            break
        if z in cuts:
            out["status"] = "repeated_cut_error"
            break
        cuts.add(z)
        m.addConstr(gp.quicksum(z[j] * q[j] for j in range(N)) <=
                    (K if gap_objective else Q))
    else:
        out["status"] = "time_limit"
    return out


if __name__ == "__main__":
    lower = next((int(a.split("=", 1)[1]) for a in sys.argv
                  if a.startswith("--mincross=")), 0)
    grid = next((int(a.split("=", 1)[1]) for a in sys.argv
                 if a.startswith("--grid=")), 8)
    print(json.dumps(search(Q=grid, min_cross_price=lower,
                            gap_objective="--maximize-local" not in sys.argv)),
          flush=True)
