"""Finite exact-state (floating LP) diagnostic, not an unrestricted proof."""
import os
os.environ.setdefault('OPENBLAS_NUM_THREADS','1')
import argparse, json, time
import numpy as np
import networkx as nx
from scipy.optimize import linprog
from scipy.sparse import coo_matrix


def local_extreme(n,edges,D,q):
 A=np.array([[int(v in e) for e in edges] for v in range(n)],dtype=float)
 r=linprog(-q,A_ub=A,b_ub=D,bounds=(0,None),method='highs')
 if not r.success: raise RuntimeError(r.message)
 return np.where(r.x>1e-9,r.x,0)


def probs(d):
 k=len(d); p=(1+2*np.array(d))/3
 out={}
 for mask in range(1<<k):
  bits=np.array([(mask>>i)&1 for i in range(k)])
  out[mask]=.75*float(np.prod(np.where(bits,p,1-p)))
 ts=sorted(set([0.,1.]+list(p)))
 for lo,hi in zip(ts,ts[1:]):
  mid=(lo+hi)/2
  mask=sum(1<<i for i in range(k) if mid<p[i])
  out[mask]+=.25*(hi-lo)
 return {mask:pr for mask,pr in out.items() if pr>1e-14}


def retention(n,edges,y,pairid,d):
 # z[state,e] is unconditional expected fluid contribution in that state.
 keep=[i for i,z in enumerate(y) if z>1e-9]
 edges=[edges[i] for i in keep]; y=np.array([y[i] for i in keep]); m=len(y)
 if not m:return 1.,None
 rr=[];cc=[];vv=[];rhs=[];bounds=[]
 for mask,pr in probs(d).items():
  available=[j for j,(u,v) in enumerate(edges) if mask>>pairid[u]&1 and mask>>pairid[v]&1]
  row0=len(rhs);rhs.extend([pr]*n)
  for j in available:
   col=len(bounds);bounds.append((0,pr*min(1,12*y[j])))
   u,v=edges[j]
   rr.extend([row0+u,row0+v,-(j+1)])
   cc.extend([col,col,col]);vv.extend([1,1,-1])
 last=len(bounds);bounds.append((0,2))
 nrows=len(rhs)
 rr=[nrows+(-r-1) if r<0 else r for r in rr]
 for j in range(m):rr.append(nrows+j);cc.append(last);vv.append(y[j])
 rhs.extend([0]*m)
 A=coo_matrix((vv,(rr,cc)),shape=(len(rhs),last+1)).tocsr()
 c=np.zeros(last+1);c[-1]=-1
 r=linprog(c,A_ub=A,b_ub=rhs,bounds=bounds,method='highs')
 if not r.success:raise RuntimeError(r.message)
 return float(r.x[-1]),r


def main():
 ap=argparse.ArgumentParser();ap.add_argument('--cases',type=int,default=3000);ap.add_argument('--seed',type=int,default=202610041);ap.add_argument('--output',default='oct4_branching_hybrid_global_lp_probe_result.json');args=ap.parse_args()
 rng=np.random.default_rng(args.seed);best=100.;start=time.time()
 palette=np.array([0,1/64,1/16,1/8,1/4,3/8,1/2,5/8,3/4,7/8,1.])
 for case in range(args.cases):
  n=int(rng.choice([8,10,12,14]))
  # Uniform random labelled tree, branch-rich caterpillar, or sparse general support.
  mode=case%4
  if mode==0:
   G=nx.from_prufer_sequence(rng.integers(0,n,size=n-2).tolist())
  elif mode==1:
   G=nx.Graph();G.add_nodes_from(range(n));centers=n//3
   G.add_edges_from((i,i+1) for i in range(centers-1))
   G.add_edges_from((v,int(rng.integers(centers))) for v in range(centers,n))
  elif mode==2:
   G=nx.random_regular_graph(3,n,seed=int(rng.integers(2**30)))
  else:
   G=nx.gnp_random_graph(n,min(.7,4/n),seed=int(rng.integers(2**30)))
  perm=rng.permutation(n);pairs=perm.reshape(-1,2).tolist();pid=np.empty(n,dtype=int)
  for i,pair in enumerate(pairs):pid[pair]=i
  d=rng.choice(palette,size=n//2)
  D=d[pid];edges=[tuple(map(int,e)) for e in G.edges()]
  q=np.exp(rng.uniform(-3,3,len(edges)))
  y=local_extreme(n,edges,D,q)
  val,r=retention(n,edges,y,pid,d)
  if val<best-1e-8:
   best=val;record={'case':case,'n':n,'mode':mode,'pairs':pairs,'d':d.tolist(),'edges':edges,'y':y.tolist(),'q_local':q.tolist(),'retention':val,'seed':args.seed}
   with open(args.output,'w') as f:json.dump(record,f,indent=2)
   print('BEST',case,round(val,12),'n',n,'positive_edges',int(np.count_nonzero(y)),flush=True)
  if val<2/3-1e-7:
   print('COUNTEREXAMPLE_CANDIDATE',json.dumps(record),flush=True);return
  if (case+1)%100==0:print('PROGRESS',case+1,'best',best,'seconds',round(time.time()-start,1),flush=True)
 print('NO_FAILURE',args.cases,'best',best,'seconds',round(time.time()-start,1),flush=True)

if __name__=='__main__':main()
