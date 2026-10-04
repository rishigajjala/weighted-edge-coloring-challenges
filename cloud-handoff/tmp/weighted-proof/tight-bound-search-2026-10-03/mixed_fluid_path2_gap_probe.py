import itertools, numpy as np
from scipy.optimize import linprog
from math import comb

def vertices(H,b):
 H=np.asarray(H,float); b=np.asarray(b,float); n=H.shape[1]; out=[]
 for I in itertools.combinations(range(len(b)),n):
  A=H[list(I)]
  if abs(np.linalg.det(A))<1e-9: continue
  x=np.linalg.solve(A,b[list(I)])
  if np.max(H@x-b)>1e-8: continue
  if not any(np.linalg.norm(x-z,np.inf)<1e-7 for z in out):out.append(x)
 return out

# coordinates x0,x1,x2,y01,y12
H=[]; b=[]
for i in range(5):
 row=[0]*5;row[i]=-1;H.append(row);b.append(0)
for i in range(3):
 row=[0]*5;row[i]=1;H.append(row);b.append(1)

def local_vertices(w):
 h=list(H);bb=list(b)
 for i,j in [(0,3),(1,3),(1,4),(2,4)]:pass
 for i,edges in [(0,[3]),(1,[3,4]),(2,[4])]:
  row=[0]*5;row[i]=w[i]
  for e in edges:row[e]=1
  h.append(row);bb.append(1)
 return vertices(h,bb)

def global_vertices(w):
 out=[]
 for bits in itertools.product((0,1),repeat=3):
  c=[1-w[i]*bits[i] for i in range(3)]
  H2=[[-1,0],[0,-1],[1,0],[0,1],[1,1]]
  b2=[0,0,c[0],c[2],c[1]]
  for y in vertices(H2,b2):out.append(np.r_[bits,y])
 return out

best=[]
for w in itertools.product((.5,.6,.75,1),repeat=3):
 L=local_vertices(w);G=global_vertices(w)
 A=np.stack(G,axis=1)
 maxgap=(0,None)
 for x in L:
  if np.max(np.abs(x))<1e-8:continue
  z=linprog(np.ones(len(G)),A_eq=A,b_eq=x,bounds=(0,None),method='highs')
  if not z.success: raise RuntimeError((w,x,z.message))
  if z.fun>maxgap[0]:maxgap=(z.fun,x)
 best.append((maxgap[0],w,maxgap[1],len(L),len(G)))
for q in sorted(best,key=lambda x:-x[0])[:15]:
 print(round(q[0],9),q[1],np.round(q[2],6),q[3:])
print('above1.25',sum(q[0]>1.25000001 for q in best),'of',len(best))
