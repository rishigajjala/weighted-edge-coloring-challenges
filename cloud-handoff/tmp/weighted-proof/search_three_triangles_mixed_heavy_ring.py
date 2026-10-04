"""Three balanced H triangles, each H side with two weight types.

Each side has total local mean 1/2, split 1/4+1/4 between its types.
Nine meeting medium cross bundles form a ring; three have parallel small
types. The exact local/star and global/repeatable oracles come from the
generalized joint-grid module. This is a bounded lower diagnostic.
"""
import json
import sys

import search_two_triangles_k33_joint_grid as core

core.CAP = 100
profiles = [[(52,72),(56,68),(60,64)],
            [(56,68),(60,64),(52,72)],
            [(60,64),(52,72),(56,68)]]
H=[]
for tri,side_weights in enumerate(profiles):
    for (a,b),weights in zip([(0,1),(1,2),(0,2)],side_weights):
        for w in weights:
            H.append((3*tri+a,3*tri+b,w))
M=[(0,3,45),(1,4,40),(2,5,35),
   (3,7,45),(4,8,40),(5,6,35),
   (6,1,40),(7,2,35),(8,0,45),
   (0,3,20),(4,8,20),(7,2,20)]
core.H=H
core.E=H+M
core.N=len(core.E)
core.NV=9
core.NH=len(H)
core.LOCAL=[core.local_patterns(v) for v in range(core.NV)]

if __name__=='__main__':
    Q=int(sys.argv[1]) if len(sys.argv)>1 else 4
    seconds=int(sys.argv[2]) if len(sys.argv)>2 else 240
    # Each side aggregate is one half; its two type means are free.
    # Hence each triangle vertex is H-saturated.
    result=core.search(Q=Q,seconds=seconds,gap_objective=True,
                       fixed_heavy_pair_sum=0.5)
    print(json.dumps(result),flush=True)
