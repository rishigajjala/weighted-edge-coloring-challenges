"""Exact finite state enumeration, floating LP, for mixed real guard residuals."""
import os
os.environ.setdefault('OPENBLAS_NUM_THREADS','1')
import argparse,itertools,json,time,importlib.util
import numpy as np
import networkx as nx
from scipy.optimize import linprog
from scipy.sparse import coo_matrix
from pathlib import Path


def states(weights,targets,alpha=2/3):
 k=len(weights);total=np.array([sum(x) for x in targets]);out=[]
 for state in itertools.product(*[range(len(w)+1) for w in weights]):
  pind=1.;ct=1.;lo=0.;hi=1.;R=[]
  for i,z in enumerate(state):
   if z==0:
    pind*=1-alpha*total[i];lo=max(lo,alpha*total[i]);R.append(1.)
   else:
    pind*=alpha*targets[i][z-1]
    if total[i]>0:ct*=targets[i][z-1]/total[i]
    else:ct=0
    hi=min(hi,alpha*total[i]);R.append(1-weights[i][z-1])
  p=.75*pind+.25*ct*max(0.,hi-lo)
  if p>1e-13:out.append((p,np.array(R)))
 assert abs(sum(p for p,r in out)-1)<1e-8
 return out


def retention(n,edges,y,pairid,weights,targets):
 keep=[i for i,z in enumerate(y) if z>1e-9]
 edges=[edges[i] for i in keep];y=np.array([y[i] for i in keep]);m=len(y)
 if not m:return 1.
 rr=[];cc=[];vv=[];rhs=[];bounds=[]
 for prob,R in states(weights,targets):
  row0=len(rhs);rhs.extend((prob*R[pairid]).tolist())
  for j,(u,v) in enumerate(edges):
   if R[pairid[u]]<1e-12 or R[pairid[v]]<1e-12:continue
   col=len(bounds);bounds.append((0,prob*min(1,12*y[j])))
   rr.extend([row0+u,row0+v,-(j+1)]);cc.extend([col,col,col]);vv.extend([1,1,-1])
 last=len(bounds);bounds.append((0,2));nr=len(rhs)
 rr=[nr+(-r-1) if r<0 else r for r in rr]
 for j in range(m):rr.append(nr+j);cc.append(last);vv.append(y[j])
 rhs.extend([0]*m)
 A=coo_matrix((vv,(rr,cc)),shape=(len(rhs),last+1)).tocsr();c=np.zeros(last+1);c[-1]=-1
 ans=linprog(c,A_ub=A,b_ub=rhs,bounds=bounds,method='highs')
 if not ans.success:raise RuntimeError(ans.message)
 return float(ans.x[-1])


def main():
 ap=argparse.ArgumentParser();ap.add_argument('--cases',type=int,default=4000);ap.add_argument('--seed',type=int,default=202610051);ap.add_argument('--output',required=True);args=ap.parse_args()
 rng=np.random.default_rng(args.seed);best=99;start=time.time()
 xp=[0,.05,.25,.5,.75,.95,1.];wp=[.500001,.55,.65,.8,.95,1.]
 for t in range(args.cases):
  n=int(rng.choice([6,8,10]));k=n//2
  pairs=rng.permutation(n).reshape(-1,2).tolist();pid=np.empty(n,dtype=int)
  for i,pair in enumerate(pairs):pid[pair]=i
  weights=[];targets=[]
  for i in range(k):
   cat=2 if t%3==0 else 1
   w=rng.choice(wp,size=cat).tolist();x=float(rng.choice(xp));z=rng.dirichlet(np.ones(cat))
   weights.append(w);targets.append((x*z).tolist())
  D=np.array([1-sum(a*b for a,b in zip(w,x)) for w,x in zip(weights,targets)])[pid]
  mode=t%4
  if mode==0:
   G=nx.star_graph(n-1)
  elif mode==1:
   G=nx.from_prufer_sequence(rng.integers(n,size=n-2).tolist())
  elif mode==2:
   G=nx.random_regular_graph(3,n,seed=int(rng.integers(2**30)))
  else:G=nx.gnp_random_graph(n,.5,seed=int(rng.integers(2**30)))
  edges=[tuple(map(int,e)) for e in G.edges()];m=len(edges)
  A=np.array([[int(v in e) for e in edges] for v in range(n)],dtype=float)
  q=np.exp(rng.uniform(-3,3,m));r=linprog(-q,A_ub=A,b_ub=D,bounds=(0,None),method='highs')
  if not r.success:raise RuntimeError(r.message)
  y=np.where(r.x>1e-9,r.x,0);val=retention(n,edges,y,pid,weights,targets)
  if val<best-1e-9:
   best=val;record={'case':t,'n':n,'mode':mode,'pairs':pairs,'weights':weights,'targets':targets,'D':D.tolist(),'edges':edges,'y':y.tolist(),'retention':val,'seed':args.seed}
   with open(args.output,'w') as f:json.dump(record,f,indent=2)
   print('BEST',t,val,'n',n,'mode',mode,flush=True)
  if val<2/3-1e-7:
   print('COUNTEREXAMPLE_CANDIDATE',json.dumps(record),flush=True);return
  if (t+1)%100==0:print('PROGRESS',t+1,'best',best,'seconds',round(time.time()-start,1),flush=True)
 print('NO_FAILURE',args.cases,best,round(time.time()-start,1),flush=True)
if __name__=='__main__':main()
