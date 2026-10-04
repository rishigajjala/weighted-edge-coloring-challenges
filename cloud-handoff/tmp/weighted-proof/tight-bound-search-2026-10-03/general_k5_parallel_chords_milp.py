"""Targeted MILP separation for a 3/2 gap in the 12-type K5 gadget.

Integer profits q in {0,...,Q}; exact global pattern inequalities;
bilinear q*x linearized with binary profit bits. A positive incumbent is
only a candidate and must be rationally verified independently.
"""

import json
import sys

import gurobipy as gp
from gurobipy import GRB

import general_k5_parallel_chords_polar as model

core = model.core


def run(weights, Q, seconds):
    pats, nall = core.patterns(weights)
    Aeq, beq, profit, nloc = core.local_lp(weights)
    m = gp.Model("k5-parallel-gap")
    m.Params.OutputFlag = 0
    m.Params.TimeLimit = seconds
    m.Params.Threads = 3
    m.Params.MIPGap = 1e-5
    lam = [m.addVar(lb=0) for _ in range(Aeq.shape[1])]
    x = [m.addVar(lb=0, ub=100 // w) for w in weights]
    q = [m.addVar(vtype=GRB.INTEGER, lb=0, ub=Q) for _ in weights]
    K = m.addVar(vtype=GRB.INTEGER, lb=1, ub=Q * sum(100 // w for w in weights))
    bits = Q.bit_length()
    b = [[m.addVar(vtype=GRB.BINARY) for _ in range(bits)]
         for _ in weights]
    t = [[m.addVar(lb=0) for _ in range(bits)] for _ in weights]
    for i in range(Aeq.shape[0]):
        m.addConstr(gp.quicksum(Aeq[i, j] * lam[j]
                                for j in range(Aeq.shape[1])) == beq[i])
    for e, w in enumerate(weights):
        m.addConstr(x[e] == gp.quicksum(profit[e, j] * lam[j]
                                        for j in range(Aeq.shape[1])))
        m.addConstr(q[e] == gp.quicksum((2**k) * b[e][k]
                                        for k in range(bits)))
        cap = 100 // w
        for k in range(bits):
            m.addConstr(t[e][k] <= cap * b[e][k])
            m.addConstr(t[e][k] <= x[e])
            m.addConstr(t[e][k] >= x[e] - cap * (1 - b[e][k]))
    for z in pats:
        m.addConstr(gp.quicksum(int(z[e]) * q[e]
                                for e in range(len(weights))) <= K)
    m.setObjective(gp.quicksum((2**k) * t[e][k]
                               for e in range(len(weights))
                               for k in range(bits)) - 1.5 * K,
                   GRB.MAXIMIZE)
    m.optimize()
    result = {"status": m.Status, "patterns": nall,
              "maximal_patterns": len(pats), "local": nloc,
              "runtime": m.Runtime, "solution_count": m.SolCount,
              "bound": m.ObjBound if m.SolCount else None}
    if m.SolCount:
        result.update(objective=m.ObjVal,
                      profit=[round(v.X) for v in q],
                      local_point=[v.X for v in x], K=round(K.X))
    print(json.dumps(result), flush=True)


if __name__ == "__main__":
    weights = [int(t) for t in sys.argv[1].split(",")]
    Q = int(sys.argv[2])
    seconds = int(sys.argv[3])
    run(weights, Q, seconds)
