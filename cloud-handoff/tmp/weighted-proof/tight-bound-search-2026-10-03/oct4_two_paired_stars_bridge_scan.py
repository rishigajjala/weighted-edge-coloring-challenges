"""Two paired-leaf stars linked by an internal center-pair fluid edge.

Uses the hybrid-law exact-state/price oracle from oct4_unit_guard_hybrid_octapolar.
This is a targeted general-graph overlap not covered by disjoint stars.
"""
import itertools
import numpy as np
from scipy.spatial import HalfspaceIntersection
import oct4_unit_guard_hybrid_octapolar as o

o.EDGES=[(0,2),(1,2),(3,4),(3,5),(2,3)]
o.NE=len(o.EDGES)
o.A=np.array([[int(v in e) for e in o.EDGES] for v in range(6)],dtype=float)

def vertices(D):
    b=np.array([D[v//2] for v in range(6)]+[0.]*o.NE)
    A=np.r_[o.A,-np.eye(o.NE)]
    interior=np.ones(o.NE)*min(D)/8
    return np.unique(np.round(HalfspaceIntersection(np.c_[A,-b],interior).intersections,10),axis=0)

def main():
    grid=[1/6,1/3,1/2,2/3,5/6,1.]
    best=(0,None);count=0
    for D in itertools.product(grid,repeat=3):
        for y in vertices(D):
            if max(y)<1e-9:continue
            ratio,q,steps=o.profit_oracle(D,y)
            count+=1
            if ratio>best[0]+1e-8:
                best=(ratio,(D,y.tolist(),q.tolist(),steps))
                print('BEST',count,best,flush=True)
    print('FINAL',count,best,flush=True)

if __name__=='__main__':main()
