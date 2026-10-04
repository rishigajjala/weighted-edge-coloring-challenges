"""Exploratory full local/global hull gap on mixed-bundle bipartite cycles.

Every type has weight >1/3. The oracle optimizes both local demands and
dual profits heuristically, with repeatable integer configurations.
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
rng = np.random.default_rng(2026100304)

def main():
    supports = [
        ([(0,2),(0,2),(0,3),(0,3),(1,2),(1,2),(1,3),(1,3)],4),
        ([(i,3+j) for i in range(3) for j in range(3)],6),
    ]
    alphabet = np.array([21,23,25,27,29,31,33,35,37,39,41,43,45,47,49,51,53,55,57,60])
    best = (4/3, None)
    for it in range(4000):
        edges,nv=supports[it%2]
        weights = rng.choice(alphabet,size=len(edges)).tolist()
        if it%4==0:
            # Build complementary heavy-medium pairs on each C4 bundle.
            ww=rng.choice([21,23,25,27,29],size=4).tolist()
            weights=[z for w in ww for z in (w,60-w)]
        try:
            ratio,data=oracle.score(edges,weights,nv,tries=8)
        except Exception as exc:
            print('ERROR',it,repr(exc),flush=True)
            continue
        if ratio>best[0]+1e-7:
            best=(ratio,{'iteration':it,'ratio':ratio,'edges':edges,
                         'weights':weights,'demand':data[0],
                         'dual':data[1],'pattern_count':data[2]})
            print('BEST',json.dumps(best[1]),flush=True)
        if it%100==0:
            print('PROGRESS',it,'best',best[0],flush=True)
    print('FINAL',json.dumps({'best':best[1],'threshold':4/3}),flush=True)

if __name__=='__main__':main()
