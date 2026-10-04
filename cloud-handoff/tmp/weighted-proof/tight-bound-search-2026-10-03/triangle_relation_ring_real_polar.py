"""All-real-profit polar optimization on the scalable triangle-relation ring.

Each of k heavy matching blockers (weight h>1/2) links two ports. Each
successive port pair has a unit direct edge and a two-spoke divisible
fluid star. Original local hull is given by simple port inequalities.
The global one-color polytope is enumerated through blocker bits and
dominant relation actions; a spatial MILP maximizes q·x over its polar.
Numerical optimizer bounds are diagnostics, not rational proof.
"""

import itertools
import json
import sys

import gurobipy as gp
from gurobipy import GRB


def rel_options(h, zi, zj):
    r=1-h
    if zi==0 and zj==0:
        return [(1,0,0),(0,1,0),(0,0,1)]
    if zi==1 and zj==1:
        return [(0,r,r)]
    if zi==1:
        return [(0,r,1-r),(0,0,1)]
    return [(0,1-r,r),(0,1,0)]


def global_patterns(k,h):
    seen=set()
    for z in itertools.product((0,1),repeat=k):
        opts=[rel_options(h,z[i],z[(i+1)%k]) for i in range(k)]
        for choices in itertools.product(*opts):
            p=[t[0] for t in choices]
            yl=[t[1] for t in choices]
            yr=[t[2] for t in choices]
            seen.add(tuple(round(t,12) for t in (*z,*p,*yl,*yr)))
    return list(seen)


def run(k,h,seconds):
    assert k>=3 and .5<h<=1
    pats=global_patterns(k,h)
    m=gp.Model("triangle-ring-real-polar")
    m.Params.OutputFlag=0
    m.Params.NonConvex=2
    m.Params.Threads=3
    m.Params.TimeLimit=seconds
    m.Params.MIPGap=1e-6
    x=[m.addVar(lb=0,ub=1) for _ in range(k)]
    p=[m.addVar(lb=0,ub=1) for _ in range(k)]
    yl=[m.addVar(lb=0,ub=1) for _ in range(k)]
    yr=[m.addVar(lb=0,ub=1) for _ in range(k)]
    q=[m.addVar(lb=0,ub=1) for _ in range(4*k)]
    for i in range(k):
        j=(i+1)%k
        m.addConstr(x[i]+p[i]<=1)
        m.addConstr(x[j]+p[i]<=1)
        m.addConstr(h*x[i]+p[i]+yl[i]<=1)
        m.addConstr(h*x[j]+p[i]+yr[i]<=1)
        m.addConstr(yl[i]+yr[i]<=1)
    for v in pats:
        m.addConstr(gp.quicksum(v[i]*q[i] for i in range(4*k))<=1)
    xx=x+p+yl+yr
    m.setObjective(gp.quicksum(q[i]*xx[i] for i in range(4*k)),GRB.MAXIMIZE)
    m.optimize()
    result={"k":k,"h":h,"patterns":len(pats),"status":m.Status,
            "runtime":m.Runtime,"solutions":m.SolCount,
            "bound":m.ObjBound if m.SolCount else None}
    if m.SolCount:
        result.update(value=m.ObjVal,
                      q=[round(t.X,8) for t in q],
                      x=[round(t.X,8) for t in xx])
    print(json.dumps(result),flush=True)


if __name__=="__main__":
    run(int(sys.argv[1]),float(sys.argv[2]),int(sys.argv[3]))
