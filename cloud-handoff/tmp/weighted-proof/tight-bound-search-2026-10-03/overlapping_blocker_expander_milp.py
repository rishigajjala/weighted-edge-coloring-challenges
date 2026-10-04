"""Targeted larger physical network of triangle factors and overlapping blockers.

The local target has factor phase A vs B+C half/half, and each of two
unit blockers at every port with marginal 1/4. Repeated copies convert
these marginals into physical demands. This MILP computes the exact
one-color maximum for random bipartite degree-two blocker networks.
"""
import sys
import numpy as np
import gurobipy as gp
from gurobipy import GRB

nf=int(sys.argv[1]) if len(sys.argv)>1 else 20
seed=int(sys.argv[2]) if len(sys.argv)>2 else 20261003
c=float(sys.argv[3]) if len(sys.argv)>3 else 1.5
assert nf%2==0
nside=nf//2
nports=3*nside
rng=np.random.default_rng(seed)
perm=rng.permutation(nports)
left=np.r_[np.arange(nports),np.arange(nports)]
right=np.r_[np.arange(nports),perm]
ne=len(left)

m=gp.Model('triangle-factor-shared-port-blockers')
m.Params.OutputFlag=0
m.Params.MIPGap=0
m.Params.TimeLimit=120
s=m.addVars(nf,3,vtype=GRB.BINARY,name='spoke')
z=m.addVars(ne,vtype=GRB.BINARY,name='blocker')
for f in range(nf):
    m.addConstr(s[f,0]+.5*s[f,1]+.5*s[f,2]<=1)
for side in range(2):
    ends=left if side==0 else right
    for p in range(nports):
        f=p//3+side*nside
        typ=p%3
        m.addConstr(s[f,typ]+gp.quicksum(z[e] for e in range(ne) if ends[e]==p)<=1)
m.setObjective(gp.quicksum(2*s[f,0]+s[f,1]+s[f,2] for f in range(nf))
               +c*gp.quicksum(z[e] for e in range(ne)),GRB.MAXIMIZE)
m.optimize()
local=2*nf+(.25*ne)*c
print({'nf':nf,'seed':seed,'c':c,'status':m.Status,'M':m.ObjVal if m.SolCount else None,
       'bound':m.ObjBound,'local':local,'ratio':local/m.ObjVal if m.SolCount else None,
       'perm':perm.tolist()})
