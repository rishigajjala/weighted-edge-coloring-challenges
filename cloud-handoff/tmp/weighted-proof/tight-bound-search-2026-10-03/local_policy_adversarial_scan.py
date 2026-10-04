import numpy as np
from itertools import product

rng=np.random.default_rng(14331)
for L,R,trials in [(3,3,60000),(4,4,30000)]:
 V=L+R; all_edges=np.array([(u,L+v) for u in range(L) for v in range(R)])
 states=np.array(list(product([0.,1.],repeat=V)))
 worst=(2,None)
 for trial in range(trials):
  mask=rng.random(len(all_edges))<rng.uniform(.2,1.)
  E=all_edges[mask]
  if not len(E):continue
  inc=np.zeros((len(E),V))
  inc[np.arange(len(E)),E[:,0]]=1;inc[np.arange(len(E)),E[:,1]]=1
  alpha_shape=10**rng.uniform(-1.3,.5)
  y=rng.dirichlet(np.ones(len(E))*alpha_shape)*rng.uniform(.1,4)
  deg=y@inc
  if max(deg)>1:y=y/max(deg);deg=deg/max(deg)
  D=deg+(1-deg)*rng.random(V)**rng.uniform(.15,6)
  p=.25+.75*D
  probs=np.prod(np.where(states==1,p,1-p),axis=1)
  t=np.minimum((4/3)*y/(p[E[:,0]]*p[E[:,1]]),12*y)
  active=(states[:,E[:,0]]*states[:,E[:,1]])*t
  load=active@inc
  denom=np.maximum.reduce([np.ones_like(active),load[:,E[:,0]],load[:,E[:,1]]])
  exp=probs@(active/denom)
  ratios=exp/y
  i=np.argmin(ratios)
  if ratios[i]<worst[0]:
   worst=(ratios[i],(L,R,trial,E.copy(),y.copy(),D.copy(),i))
   if ratios[i]<.7499:break
 print('case',L,R,'worst',worst,flush=True)
