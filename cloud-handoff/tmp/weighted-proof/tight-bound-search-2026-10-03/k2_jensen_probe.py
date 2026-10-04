import numpy as np
from itertools import product
rng=np.random.default_rng(8468)
K=2.
for L,R,trials in [(3,3,60000),(4,4,30000)]:
 V=L+R;all_edges=np.array([(u,L+v) for u in range(L) for v in range(R)])
 states=np.array(list(product([0.,1.],repeat=V)))
 worst=(2,None)
 for trial in range(trials):
  E=all_edges[rng.random(len(all_edges))<rng.uniform(.2,1)]
  if not len(E):continue
  inc=np.zeros((len(E),V));inc[np.arange(len(E)),E[:,0]]=1;inc[np.arange(len(E)),E[:,1]]=1
  y=rng.dirichlet(np.ones(len(E))*10**rng.uniform(-1.3,.6))*rng.uniform(.1,4)
  deg=y@inc
  if max(deg)>1:y=y/max(deg);deg=deg/max(deg)
  D=deg+(1-deg)*rng.random(V)**rng.uniform(.1,6)
  p=.25+.75*D
  probs=np.prod(np.where(states==1,p,1-p),axis=1)
  t=np.minimum(K*y/(p[E[:,0]]*p[E[:,1]]),12*y)
  active=(states[:,E[:,0]]*states[:,E[:,1]])*t
  load=active@inc
  denom=np.maximum.reduce([np.ones_like(active),load[:,E[:,0]],load[:,E[:,1]]])
  cond_mean=(probs@((states[:,E[:,0]]*states[:,E[:,1]])*denom))/(p[E[:,0]]*p[E[:,1]])
  bound=(4/3)*np.minimum(K,12*p[E[:,0]]*p[E[:,1]])
  ratios=bound/cond_mean
  i=np.argmin(ratios)
  if ratios[i]<worst[0]:
   worst=(ratios[i],(trial,E.copy(),y.copy(),D.copy(),i,cond_mean[i],bound[i]))
   if ratios[i]<.9999:break
 print(L,R,worst,flush=True)
