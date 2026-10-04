"""Full-configuration LP search: heavy and medium C8 factors of K4,4.

Heavy edges are shared guards; every vertex has two heavy and two medium
edge types. The two C8 factors are edge-disjoint. Run from project root.
"""
import json
import sys
from pathlib import Path

import numpy as np
import scipy.optimize
import scipy.spatial

HERE = Path(__file__).resolve().parent
sys.path.insert(0, str(HERE))
import bipartite_mixed_path_search as oracle

oracle.CAP = 60
rng = np.random.default_rng(2026100303)
H = [(i, 4 + (i + shift) % 4) for shift in (0, 1) for i in range(4)]
M = [(i, 4 + (i + shift) % 4) for shift in (2, 3) for i in range(4)]
EDGES = H + M


def local_full_pair_possible(weights):
    for v in range(8):
        hh = sorted(weights[i] for i, e in enumerate(H) if v in e)
        mm = sorted(weights[8+i] for i, e in enumerate(M) if v in e)
        if hh[0] + mm[1] > 60 or hh[1] + mm[0] > 60:
            return False
    return True


def main():
    n = 0
    best = (4/3, None)
    for it in range(10000):
        hw = rng.choice([32, 34, 36, 38], size=8).tolist()
        mw = rng.choice([22, 24, 26, 28], size=8).tolist()
        weights = hw + mw
        if not local_full_pair_possible(weights):
            continue
        n += 1
        try:
            ratio, data = oracle.score(EDGES, weights, 8, tries=10)
        except Exception as exc:
            print('ERROR', it, repr(exc), flush=True)
            continue
        if ratio > best[0] + 1e-7:
            best = (ratio, {'ratio': ratio, 'weights': weights,
                            'edges': EDGES, 'demand': data[0],
                            'dual': data[1], 'pattern_count': data[2]})
            print('BEST', json.dumps(best[1]), flush=True)
        if n % 5 == 0:
            print('PROGRESS', n, 'tested; best', best[0], flush=True)
        if n >= 40:
            break
    print('FINAL', json.dumps({'valid_cases': n, 'best': best[1],
                               'threshold': 4/3}), flush=True)


if __name__ == '__main__':
    main()
