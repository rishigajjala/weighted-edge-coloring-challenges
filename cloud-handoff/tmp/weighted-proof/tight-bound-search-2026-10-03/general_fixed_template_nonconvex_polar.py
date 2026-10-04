"""All-real-profit polar optimization for a fixed weighted small graph.

Uses spatial branch-and-bound for the bilinear max q·x, subject to
q≥0, all global pattern inequalities q·z≤1, and exact local LP x.
Only a proved optimal solver bound certifies the fixed template.
"""

import json
import sys

import gurobipy as gp
from gurobipy import GRB

import general_k5_parallel_chords_polar as model

core = model.core


def run(weights, seconds):
    pats, nall = core.patterns(weights)
    Aeq, beq, profit, nloc = core.local_lp(weights)
    m = gp.Model("real-polar")
    m.Params.OutputFlag = 0
    m.Params.TimeLimit = seconds
    m.Params.Threads = 3
    m.Params.NonConvex = 2
    m.Params.MIPGap = 1e-7
    lam = [m.addVar(lb=0) for _ in range(Aeq.shape[1])]
    x = [m.addVar(lb=0, ub=100 // w) for w in weights]
    q = [m.addVar(lb=0, ub=1) for _ in weights]
    for i in range(Aeq.shape[0]):
        m.addConstr(gp.quicksum(Aeq[i, j] * lam[j]
                                for j in range(Aeq.shape[1])) == beq[i])
    for e in range(len(weights)):
        m.addConstr(x[e] == gp.quicksum(profit[e, j] * lam[j]
                                        for j in range(Aeq.shape[1])))
    for z in pats:
        m.addConstr(gp.quicksum(int(z[e]) * q[e]
                                for e in range(len(weights))) <= 1)
    m.setObjective(gp.quicksum(q[e] * x[e] for e in range(len(weights))),
                   GRB.MAXIMIZE)
    m.optimize()
    result = {"status": m.Status, "patterns": nall,
              "maximal_patterns": len(pats), "local": nloc,
              "runtime": m.Runtime, "solution_count": m.SolCount,
              "bound": m.ObjBound if m.SolCount else None}
    if m.SolCount:
        result.update(objective=m.ObjVal,
                      profit=[v.X for v in q],
                      local_point=[v.X for v in x])
    print(json.dumps(result), flush=True)


if __name__ == "__main__":
    weights = [int(t) for t in sys.argv[1].split(",")]
    seconds = int(sys.argv[2])
    if len(sys.argv) > 3 and sys.argv[3] == "heavycycle":
        core.EDGES = [(0, 1), (0, 1), (1, 2), (1, 2),
                      (2, 3), (2, 3), (3, 4), (3, 4),
                      (4, 0), (4, 0),
                      (0, 2), (1, 3), (2, 4), (3, 0), (4, 1)]
        core.D = len(core.EDGES)
    run(weights, seconds)
