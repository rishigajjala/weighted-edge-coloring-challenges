"""Column-generation polar for a fixed two-port target x=1/2; diagnostic only."""
import argparse
import numpy as np
from scipy.optimize import linprog, milp, LinearConstraint, Bounds
from oct4_port_phase_frustration_probe import sample


def polar(w, triples, orig_l, orig_r, limit=120):
    m = len(orig_l)
    E = len(w)
    B = np.zeros((m, E))
    for j, (u, v) in enumerate(triples):
        B[orig_l[u], j] = w[j]
        B[m // 2 + orig_r[v], j] = w[j]
    pats = np.eye(E)
    ub = np.floor(1 / w)
    for it in range(limit):
        lp = linprog(-np.ones(E) / 2, A_ub=pats, b_ub=np.ones(len(pats)),
                     bounds=[(0, None)] * E, method="highs")
        if lp.status:
            return None, it, lp.message
        q = lp.x
        price = milp(-q, integrality=np.ones(E), bounds=Bounds(np.zeros(E), ub),
                     constraints=LinearConstraint(B, -np.inf, np.ones(m)),
                     options={"time_limit": 8.0, "mip_rel_gap": 1e-8})
        if price.status:
            return None, it, "pricing incomplete"
        if -price.fun <= 1 + 1e-7:
            return -lp.fun, it, q
        pat = np.rint(price.x).astype(int)
        pats = np.vstack((pats, pat))
    return None, limit, "iteration cap"


def main():
    p = argparse.ArgumentParser()
    p.add_argument("--ports", type=int, default=6)
    p.add_argument("--trials", type=int, default=5)
    p.add_argument("--delta", type=float, default=.20)
    args = p.parse_args()
    rng = np.random.default_rng(99931)
    for j in range(args.trials):
        _, _, w, triples, orig_l, orig_r, _ = sample(args.ports, rng, args.delta)
        val, it, cert = polar(w, triples, orig_l, orig_r)
        print(j, val, it, cert if isinstance(cert, str) else "", flush=True)


if __name__ == "__main__":
    main()
