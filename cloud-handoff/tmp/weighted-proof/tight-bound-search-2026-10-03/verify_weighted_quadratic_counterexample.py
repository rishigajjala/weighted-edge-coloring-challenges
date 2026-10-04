"""Exact arithmetic checks for the cube construction.

Universal optimality is proved in weighted_quadratic_balancing_counterexample.md;
this verifier checks the construction and both explicit assignments.
"""
from fractions import Fraction as F
import json

d = 9
m = 2**d
edges = [(v, v ^ (1 << j)) for v in range(m) for j in range(d)
         if v < (v ^ (1 << j))]
assert len(edges) == m*d//2
degree = [0]*m
for u,v in edges:
    degree[u] += 1
    degree[v] += 1
assert set(degree) == {d}

def discrepancies(ports, cube):
    result = [F(p) for p in ports]
    for (u,v), s in zip(edges,cube):
        result[u] -= F(s,d)
        result[v] -= F(s,d)
    return [F(5,1024)*sum(ports)] + result

minimum = discrepancies([1]*m, [1]*len(edges))
assert minimum[0] == F(5,2)
assert all(z == 0 for z in minimum[1:])
assert sum(z*z for z in minimum) == F(25,4)
assert F(4,81) > F(25,512)

ports = [1 if (v & 1) == 0 else -1 for v in range(m)]
cube = [ports[u] if ports[u] == ports[v] else 1 for u,v in edges]
balanced = discrepancies(ports,cube)
assert balanced[0] == 0
assert max(map(abs,balanced)) == F(2,9)
assert sum(z*z for z in balanced) == F(1024,81)

print(json.dumps(dict(rows=m+1, columns=m+len(edges), max_entries_per_column=2,
    minimizing_root_gap=str(minimum[0]), minimizing_energy=str(F(25,4)),
    balanced_max_gap=str(max(map(abs,balanced))),
    balanced_energy=str(sum(z*z for z in balanced)),
    per_minority_energy_margin=str(F(4,81)-F(25,512)))))
