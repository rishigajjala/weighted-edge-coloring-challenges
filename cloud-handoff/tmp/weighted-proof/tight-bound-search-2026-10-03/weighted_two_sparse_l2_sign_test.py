"""Test whether every global L2-minimizing sign has discrepancy <=2.

Columns have at most two nonnegative entries in [0,1]. Exhaustive over
all signings for each sampled matrix. A counterexample is rational
because entries are chosen on a small integer grid.
"""
import json
import sys

import numpy as np


def sign_table(m):
    bits = ((np.arange(1 << (m-1))[:,None] >> np.arange(m-1)) & 1)
    return np.column_stack((np.ones(len(bits), dtype=np.int8), 2*bits-1))


def main():
    rng = np.random.default_rng(31102026)
    scale = 12
    tested = 0
    record = 0
    record_data = None
    for n in range(3,8):
        for m in range(5,16):
            signs = sign_table(m)
            for rep in range(400):
                aa = np.zeros((n,m), dtype=np.int16)
                for e in range(m):
                    u,v = rng.choice(n,size=2,replace=False)
                    aa[u,e] = rng.integers(1,scale+1)
                    aa[v,e] = rng.choice([-1,1])*rng.integers(1,scale+1)
                ss = signs @ aa.T
                sq = np.sum(ss.astype(np.int64)**2,axis=1)
                minima = np.flatnonzero(sq == np.min(sq))
                maximum = int(np.max(np.abs(ss[minima])))
                if maximum > record:
                    record = maximum
                    record_data = (n,m,aa.tolist(),signs[minima[0]].tolist(),ss[minima[0]].tolist())
                bad = [i for i in minima if np.max(np.abs(ss[i])) > 2*scale]
                tested += 1
                if bad:
                    i = bad[0]
                    print(json.dumps({"tested":tested,"n":n,"m":m,"scale":scale,
                                      "matrix":aa.tolist(),"minimum_sq":int(sq[i]),
                                      "sign":signs[i].tolist(),
                                      "sum":ss[i].tolist(),"all_minimizers":len(minima)}),flush=True)
                    return
            print("PROGRESS",n,m,tested,flush=True)
    print("NO_COUNTEREXAMPLE",tested,"RECORD",record,"SCALE",scale,
          "DATA",json.dumps(record_data),flush=True)


if __name__ == "__main__":
    main()
