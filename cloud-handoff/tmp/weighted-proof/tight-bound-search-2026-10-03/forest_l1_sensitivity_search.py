"""Adversarial numerical audit of the capped forest optimum L1 claim."""

import argparse
import numpy as np
from scipy.optimize import linprog


def random_tree(rng, n):
    return [(i, int(rng.integers(i))) for i in range(1, n)]


def solve(n, edges, cap, r, profit):
    a = np.zeros((n, len(edges)))
    for j, (u, v) in enumerate(edges):
        a[u, j] = a[v, j] = 1
    out = linprog(-profit, A_ub=a, b_ub=r, bounds=list(zip(np.zeros(len(edges)), cap)), method="highs")
    if not out.success:
        raise RuntimeError(out.message)
    return out.x


def diameter(n, edges):
    nbr = [[] for _ in range(n)]
    for u, v in edges:
        nbr[u].append(v)
        nbr[v].append(u)
    best = 0
    for root in range(n):
        dis = [-1] * n
        dis[root] = 0
        todo = [root]
        for u in todo:
            for v in nbr[u]:
                if dis[v] < 0:
                    dis[v] = dis[u] + 1
                    todo.append(v)
        best = max(best, max(dis))
    return best


if __name__ == "__main__":
    parser = argparse.ArgumentParser()
    parser.add_argument("--trials", type=int, default=10000)
    args = parser.parse_args()
    rng = np.random.default_rng(9396)
    worst = (0, None)
    for k in range(args.trials):
        n = int(rng.integers(2, 13))
        edges = random_tree(rng, n)
        a = rng.dirichlet(np.ones(len(edges)))
        # Scale targets so each vertex target degree is <= 1.
        deg = np.zeros(n)
        for j,(u,v) in enumerate(edges):
            deg[u] += a[j]
            deg[v] += a[j]
        a /= max(1, deg.max())
        cap = 12*a
        r = rng.random(n)
        q = rng.normal(size=len(edges)) + 1e-6*rng.random(len(edges))
        v = int(rng.integers(n))
        delta = float(10 ** rng.uniform(-5, -.3))
        f = solve(n,edges,cap,r,q)
        rr = r.copy();rr[v] += delta
        g = solve(n,edges,cap,rr,q)
        ratio = np.abs(f-g).sum()/delta
        if ratio > worst[0]:
            worst = (ratio, (k,n,diameter(n,edges),v,delta,edges,a,r,q,f,g))
            print("record", k, ratio, "diam", worst[1][2], flush=True)
        if ratio > 2*diameter(n,edges)+1e-5:
            print("COUNTEREXAMPLE", worst)
            break
    print("final", worst[0], "diam", worst[1][2] if worst[1] else None)
