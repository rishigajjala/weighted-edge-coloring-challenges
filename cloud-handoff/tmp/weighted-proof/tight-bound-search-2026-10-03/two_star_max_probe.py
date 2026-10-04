import numpy as np
from itertools import product
rng=np.random.default_rng(803)
K=2
for m,n,trials in [(2,2,100000),(3,3,100000),(4,4,100000)]:
 Sm=np.array(list(product([0.,1.],repeat=m)))
 Sn=np.array(list(product([0.,1.],repeat=n)))
 worst=(2,None)
 for trial in range(trials):
  ya=rng.dirichlet(np.ones(m)*10**rng.uniform(-1.5,.5))
  yb=rng.dirichlet(np.ones(n)*10**rng.uniform(-1.5,.5))
  pmin_a=.25+.75*ya;pmin_b=.25+.75*yb
  pa=pmin_a+(1-pmin_a)*rng.random(m)**rng.uniform(.1,5)
  pb=pmin_b+(1-pmin_b)*rng.random(n)**rng.uniform(.1,5)
  ba=np.minimum(K*ya/pa,12*ya)
  bb=np.minimum(K*yb/pb,12*yb)
  prob_a=np.prod(np.where(Sm==1,pa,1-pa),axis=1)
  prob_b=np.prod(np.where(Sn==1,pb,1-pb),axis=1)
  Xa=Sm@ba;Xb=Sn@bb
  score=prob_a@np.maximum(1,np.maximum.outer(Xa,Xb))@prob_b
  if score>worst[0]:worst=(score,(ya.copy(),pa.copy(),yb.copy(),pb.copy()))
  if score>8/3+1e-4:break
 print(m,n,worst,flush=True)
