"""Exhaustive small weighted-path diagnostic of a fixed heavy law; not proof."""
from itertools import product
from scipy.optimize import linprog

V=6
E=[(i,i+1) for i in range(V-1)]
A=[[int(v in e) for e in E] for v in range(V)]

def pairings(vertices):
 if not vertices:
  yield ()
  return
 a=vertices[0]
 for j in range(1,len(vertices)):
  b=vertices[j]
  for rest in pairings(vertices[1:j]+vertices[j+1:]):
   yield ((a,b),)+rest

def lp(q,deg,caps=None):
 bounds=[(0,None if caps is None else c) for c in (caps if caps is not None else E)]
 r=linprog([-float(x) for x in q],A_ub=A,b_ub=deg,bounds=bounds,method='highs')
 if not r.success:raise RuntimeError(r.message)
 return -r.fun,r.x

best=(1e9,None);count=0
for P in pairings(tuple(range(V))):
 ix={v:j for j,pair in enumerate(P) for v in pair}
 for d in product((.25,.5,.75),repeat=3):
  D=[d[ix[v]] for v in range(V)]
  p=[(1+2*z)/3 for z in d]
  for q in product((1,2),repeat=5):
   target,y=lp(q,D)
   caps=12*y
   vals={}
   for b in product((0,1),repeat=3):
    deg=[b[ix[v]] for v in range(V)]
    vals[b]=lp(q,deg,caps)[0]
   ind=0.
   for b,val in vals.items():
    prob=1.
    for bit,pi in zip(b,p):prob*=pi if bit else 1-pi
    ind+=prob*val
   ts=sorted(set([0.,1.]+p)); com=0.
   for lo,hi in zip(ts,ts[1:]):
    u=(lo+hi)/2
    b=tuple(int(u<=pi) for pi in p)
    com+=(hi-lo)*vals[b]
   got=.75*ind+.25*com
   gap=got-(2/3)*target
   count+=1
   if gap<best[0]-1e-10:best=(gap,(P,d,q,target,got,ind,com,tuple(y)))
print('instances',count,'best',best,flush=True)
