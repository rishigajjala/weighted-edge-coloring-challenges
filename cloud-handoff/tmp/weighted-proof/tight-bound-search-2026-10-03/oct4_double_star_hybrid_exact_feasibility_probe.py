"""Targeted finite LP feasibility probe for the first nonstar branch interaction."""
from itertools import product
from scipy.optimize import linprog

V=6
E=((0,1),(1,2),(1,4),(3,4),(4,5))
A=[[int(v in e) for e in E] for v in range(V)]
alpha=2/3

def pairings(vertices):
 if not vertices:
  yield ()
  return
 v=vertices[0]
 for j in range(1,len(vertices)):
  w=vertices[j]
  for rest in pairings(vertices[1:j]+vertices[j+1:]):
   yield ((v,w),)+rest

def local_y(D,q):
 r=linprog([-float(a) for a in q],A_ub=A,b_ub=D,bounds=[(0,None)]*len(E),method='highs')
 if not r.success:raise RuntimeError(r.message)
 return tuple(round(max(0.,float(z)),10) for z in r.x)

def state_probs(p):
 out={}
 ts=sorted(set((0.,1.)+tuple(p)))
 for B in product((0,1),repeat=3):
  ind=1.
  for bit,pi in zip(B,p):ind*=pi if bit else 1-pi
  com=0.
  for lo,hi in zip(ts,ts[1:]):
   u=(lo+hi)/2
   if tuple(int(u<=pi) for pi in p)==B:com+=hi-lo
  out[B]=.75*ind+.25*com
 return out

def feasible(y,ix,p):
 probs=state_probs(p)
 states=[B for B in product((0,1),repeat=3) if probs[B]>1e-12]
 m=len(E); nvar=len(states)*m
 rows=[];rhs=[]
 for j,B in enumerate(states):
  for v in range(V):
   row=[0.]*nvar
   for e in range(m):row[j*m+e]=A[v][e]
   rows.append(row);rhs.append(float(B[ix[v]]))
 for e in range(m):
  row=[0.]*nvar
  for j,B in enumerate(states):row[j*m+e]=-probs[B]
  rows.append(row);rhs.append(-alpha*y[e])
 bounds=[(0,12*y[e]) for B in states for e in range(m)]
 r=linprog([0.]*nvar,A_ub=rows,b_ub=rhs,bounds=bounds,method='highs')
 return r.success,r

count=0; uniques=0
for P in pairings(tuple(range(V))):
 ix={v:j for j,pair in enumerate(P) for v in pair}
 for d in product((.25,.5,.75,1.),repeat=3):
  D=tuple(d[ix[v]] for v in range(V))
  p=tuple((1+2*z)/3 for z in d)
  seen=set()
  for q in product((1.,2.),repeat=len(E)):
   y=local_y(D,q)
   count+=1
   if y in seen:continue
   seen.add(y);uniques+=1
   ok,r=feasible(y,ix,p)
   if not ok:
    print('COUNTER',P,d,q,y,'status',r.status,r.message,'counts',count,uniques,flush=True)
    raise SystemExit(0)
print('NO COUNTER',count,'local objectives',uniques,'distinct target instances',flush=True)
