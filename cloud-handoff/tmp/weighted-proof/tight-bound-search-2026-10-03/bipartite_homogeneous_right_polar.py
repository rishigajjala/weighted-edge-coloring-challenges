"""Complete small-alphabet sweep of homogeneous-right K3,3 templates.

For each template, optimize over *all* polar profit vertices rather than
sampling dual directions. Numerical Qhull/HiGHS; candidates need exact audit.
"""
import itertools
import json
from pathlib import Path
import sys

HERE = Path(__file__).resolve().parent
sys.path.insert(0, str(HERE))
from bipartite_rank_two_polar_gap import score

edges = [(i, 3+j) for i in range(3) for j in range(3)]
alphabet = [35, 40, 45, 55, 60, 65]
best = {"gap": 1.0}
cases = 0
for cols in itertools.product(alphabet, repeat=3):
    weights = [cols[j] for i in range(3) for j in range(3)]
    result = score(edges, weights, 6)
    cases += 1
    if result["gap"] > best["gap"] + 1e-8:
        best = result
        print("BEST", json.dumps({"columns": cols, **best}), flush=True)
print("FINAL", json.dumps({"cases": cases, "best": best}), flush=True)
