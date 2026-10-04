import numpy as np
from itertools import product

rng=np.random.default_rng(555)
L=3;R=3;V=6
all_edges=np.array([(u,L+v) for u in range(L) for v in range(R)])
states=np.array(list(product([0.,1.],repeat=V)))
ks=[1.,1.25,1.5,1.75,2.,2.5,3.,4.,6.]
worst={k:(2.,None) for k in ks}
for trial in range(4000):
 mask=rng.random(len(all_edges))<rng.uniform(.3,1)
 E=all_edges[mask]
 if len(E)==0:continue
 y=rng.dirichlet(np.ones(len(E))*rng.uniform(.1,2))*rng.uniform(.1,3)
 deg=np.zeros(V)
 for i,(u,v) in enumerate(E):deg[u]+=y[i];deg[v]+=y[i]
 if max(deg)>1:y=y/max(deg);deg=deg/max(deg)
 D=deg+(1-deg)*rng.random(V)**rng.uniform(.3,4)
 p=.25+.75*D
 probs=np.prod(np.where(states==1,p,1-p),axis=1)
 for K in ks:
  t=np.array([min(K*y[i]/(p[u]*p[v]),12*y[i]) for i,(u,v) in enumerate(E)])
  exp=np.zeros(len(E))
  for A,prob in zip(states,probs):
   if prob<1e-15:continue
   x=np.array([t[i]*A[u]*A[v] for i,(u,v) in enumerate(E)])
   load=np.zeros(V)
   for i,(u,v) in enumerate(E):load[u]+=x[i];load[v]+=x[i]
   factor=np.minimum(1.,1./np.maximum(load,1e-100))
   z=np.array([x[i]*min(factor[u],factor[v]) for i,(u,v) in enumerate(E)])
   exp+=prob*z
  ratios=exp/y
  i=np.argmin(ratios)
  if ratios[i]<worst[K][0]:worst[K]=(ratios[i],(trial,E.copy(),y.copy(),D.copy(),i))
for K in ks:print(K,worst[K])
