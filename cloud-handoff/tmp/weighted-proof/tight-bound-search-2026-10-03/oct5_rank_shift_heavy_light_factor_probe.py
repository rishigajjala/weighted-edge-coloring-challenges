"""Structured full-count polar probe for a heavy C8 over a small K4,4."""
import numpy as np
from scipy.optimize import linprog, milp, Bounds, LinearConstraint

n=4
U=lambda i:i
V=lambda i:4+i
edges=[]
weights=[]
# The alternating heavy cycle: each U_i is joined to V_i and V_(i-1).
for i in range(n):
    edges.append((U(i),V(i)))
    edges.append((U(i),V((i-1)%n)))
# Numeric rank shifts around the eight-edge heavy cycle.
weights += [.64,.60,.56,.64,.60,.56,.60,.56]
# Small edges form K4,4. Offset 0 or 1 is low, offset 2 or 3 high.
for i in range(n):
    for j in range(n):
        edges.append((U(i),V(j)))
        weights.append(.16 if (j-i)%n in (0,1) else .20)

weights=np.array(weights)
E=len(edges)
A=np.zeros((8,E))
for j,(u,v) in enumerate(edges):
    A[u,j]=A[v,j]=weights[j]
zmax=np.floor(1/weights+1e-9).astype(int)
rows=[np.eye(E,dtype=int)[j]*zmax[j] for j in range(E)]
lp=None
for step in range(600):
    lp=linprog(-.5*np.ones(E),A_ub=np.array(rows),b_ub=np.ones(len(rows)),bounds=[(0,None)]*E,method='highs')
    if not lp.success:raise RuntimeError(lp.message)
    q=lp.x
    price=milp(-q,integrality=np.ones(E),bounds=Bounds(np.zeros(E),zmax),constraints=LinearConstraint(A,np.zeros(8),np.ones(8)),options={'mip_rel_gap':1e-10})
    if not price.success:raise RuntimeError(price.message)
    z=np.rint(price.x).astype(int)
    val=q@z
    if val<=1+1e-8:
        print('done',step,'ratio',-lp.fun,'pricing',val)
        print('heavy q',np.round(q[:8],6).tolist())
        print('small q',np.round(q[8:].reshape(4,4),6).tolist())
        print('active counts',np.count_nonzero(q[:8]),np.count_nonzero(q[8:]))
        break
    if any(np.array_equal(z,r) for r in rows):raise RuntimeError('duplicate cut')
    rows.append(z)
    if step%25==0:print('step',step,'polar upper',-lp.fun,'pricing',val,flush=True)
else:print('iteration cap',-lp.fun)
