"""Targeted finite LP diagnostic for cyclic graded guard constructions.

The scorer uses all repeatable integer color patterns and full local
configuration hulls. Alternating optimization is heuristic, so a failed
search is not a universal bound. Run from the project root.
"""
import json
import sys
from pathlib import Path

import numpy as np
import scipy.optimize  # preload system SciPy before the legacy oracle adds tmp deps
import scipy.spatial

HERE = Path(__file__).resolve().parent
sys.path.insert(0, str(HERE))
import bipartite_mixed_path_search as oracle

oracle.CAP = 60
rng = np.random.default_rng(2026100302)


def instance(core_weights, guard_weights):
    m = len(core_weights)
    edges = [(i, (i + 1) % m) for i in range(m)]
    edges += [(i, m + i) for i in range(m)]
    return edges, core_weights + guard_weights, 2 * m


def main():
    cases = []
    for m in (4, 6):
        base = [29, 27, 25, 23, 21, 20][:m]
        for rotation in range(m):
            ww = base[rotation:] + base[:rotation]
            for mode in ('outgoing_complement', 'incoming_complement',
                         'strict_incoming_incompatible', 'mixed'):
                if mode == 'outgoing_complement':
                    hh = [60 - w for w in ww]
                elif mode == 'incoming_complement':
                    hh = [60 - ww[(i-1) % m] for i in range(m)]
                elif mode == 'strict_incoming_incompatible':
                    hh = [61 - min(ww[(i-1) % m], ww[i]) for i in range(m)]
                else:
                    hh = [60 - (ww[i] if i % 2 else ww[(i-1) % m])
                          for i in range(m)]
                cases.append((mode, ww, hh))
        for _ in range(40):
            ww = rng.choice([20, 22, 24, 26, 28, 30], size=m).tolist()
            hh = [60 - rng.choice([20, 22, 24, 26, 28, 30]) for _ in range(m)]
            cases.append(('random_complement', ww, hh))

    best = (4/3, None)
    for i, (mode, ww, hh) in enumerate(cases):
        edges, weights, nv = instance(ww, hh)
        try:
            ratio, data = oracle.score(edges, weights, nv, tries=14)
        except Exception as exc:
            print('ERROR', i, repr(exc), flush=True)
            continue
        if ratio > best[0] + 1e-7:
            best = (ratio, {'case': i, 'mode': mode, 'core_weights': ww,
                            'guard_weights': hh, 'ratio': ratio,
                            'demand': data[0], 'dual': data[1],
                            'pattern_count': data[2]})
            print('BEST', json.dumps(best[1]), flush=True)
        if i % 25 == 0:
            print('PROGRESS', i, len(cases), 'best', best[0], flush=True)
    print('FINAL', json.dumps({'cases': len(cases), 'best': best[1],
                               'threshold': 4/3}), flush=True)


if __name__ == '__main__':
    main()
