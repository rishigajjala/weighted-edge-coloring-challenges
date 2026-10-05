"""Numerical diagnostic of fixed hybrid recourse on mixed-weight paired stars.

All leaves are in separate heavy pairs from the center; each leaf group has
either one or both ports and aggregate fluid target Y. Conditional cap is
12*y per physical spoke. This script computes exact finite-state expectations
for sampled rational/decimal parameters but does not prove a theorem.
"""

import argparse
import itertools
import json
import numpy as np

ALPHA = 2 / 3


def residuals(types):
    # types is [(weight, original probability), ...]
    x = sum(prob for _, prob in types)
    return (np.array([1] + [1 - weight for weight, _ in types]),
            np.array([1 - ALPHA * x] + [ALPHA * prob for _, prob in types]), x)


def exact_value(groups, target, ports):
    """groups[0] is center; others are leaf pairs with ports 1 or 2."""
    rs, ps, xs = zip(*(residuals(g) for g in groups))
    states = list(itertools.product(*(range(len(r)) for r in rs)))
    def payoff(st):
        center = rs[0][st[0]]
        available = sum(min(ports[i - 1] * rs[i][st[i]], 12 * target[i - 1])
                        for i in range(1, len(groups)))
        return min(center, available)
    independent = sum(payoff(st) * np.prod([ps[i][st[i]] for i in range(len(groups))])
                      for st in states)
    cuts = sorted(set([0, 1] + [ALPHA * x for x in xs]))
    common = 0.0
    for left, right in zip(cuts[:-1], cuts[1:]):
        u = (left + right) / 2
        conditional = []
        for g, x in zip(groups, xs):
            if x == 0 or u > ALPHA * x:
                conditional.append(np.array([1] + [0] * len(g)))
            else:
                conditional.append(np.array([0] + [prob / x for _, prob in g]))
        common += (right - left) * sum(
            payoff(st) * np.prod([conditional[i][st[i]] for i in range(len(groups))])
            for st in states)
    return .75 * independent + .25 * common, independent, common


def random_case(rng, k):
    groups = []
    for _ in range(k + 1):
        x = rng.choice([rng.uniform(0, 1), 1, rng.uniform(.5, 1)])
        mix = rng.uniform(0, 1)
        w1 = rng.choice([.500001, .6, .75, 1.0])
        w2 = rng.choice([.500001, .6, .75, 1.0])
        groups.append([(w1, x * mix), (w2, x * (1 - mix))])
    ds = [1 - sum(w * x for w, x in g) for g in groups]
    ports = rng.choice([1, 2], size=k)
    raw = rng.dirichlet(np.ones(k) * rng.choice([.1, 1, 5]))
    total = ds[0] * rng.choice([1, rng.uniform(.01, 1)])
    y = np.minimum(raw * total, np.array(ports) * np.array(ds[1:]))
    return groups, y, ports, ds


def main(args):
    rng = np.random.default_rng(args.seed)
    best = (float("inf"), None)
    for trial in range(args.trials):
        k = int(rng.integers(1, args.max_groups + 1))
        groups, y, ports, ds = random_case(rng, k)
        if y.sum() < 1e-5: continue
        val, indep, common = exact_value(groups, y, ports)
        slack = val - ALPHA * y.sum()
        ratio = val / (ALPHA * y.sum())
        if ratio < best[0]:
            row = dict(trial=trial, groups=groups, y=y.tolist(), ports=ports.tolist(),
                       D=ds, expected=val, independent=indep, common=common,
                       target=ALPHA * y.sum(), slack=slack, ratio=ratio)
            best = (ratio, row)
            print(json.dumps({"best": row}), flush=True)
        if slack < -1e-8:
            print(json.dumps({"FAILURE": best[1]}), flush=True)
            break
    print(json.dumps({"summary": {"trials": args.trials, "seed": args.seed,
                                   "best_ratio": best[0]}}), flush=True)


if __name__ == "__main__":
    p = argparse.ArgumentParser()
    p.add_argument("--trials", type=int, default=10000)
    p.add_argument("--max-groups", type=int, default=4)
    p.add_argument("--seed", type=int, default=94331)
    main(p.parse_args())
