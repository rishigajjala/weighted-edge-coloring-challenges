"""Three heavy guard pairs + rank-three B-cycle; exact type-count oracle diagnostic."""
import itertools
import numpy as np
from scipy.optimize import milp,Bounds,LinearConstraint


def make(s,pl,pr,t0):
    # Vertices L0,L1,L2,R0,R1,R2. Each has A=(1-s_i,s_i) and
    # B=(one incoming s_j, two B-cycle edges), both summing to 1.
    edges=[]
    for i in range(3):edges.append((i,3+i,1-s[i],'H'))
    for i in range(3):edges.append((i,3+pl[i],s[i],'S'))
    for i in range(3):edges.append((3+i,pr[i],s[i],'S'))
    cyc=[(0,3),(1,3),(1,4),(2,4),(2,5),(0,5)]
    sL=[s[list(pr).index(i)] for i in range(3)]
    sR=[s[list(pl).index(i)] for i in range(3)]
    t=[t0,1-sR[0]-t0]
    t.append(1-sL[1]-t[1]);t.append(1-sR[1]-t[2]);t.append(1-sL[2]-t[3]);t.append(1-sR[2]-t[4])
    if abs(t[5]+t[0]-(1-sL[0]))>1e-8:return None
    if min(t)<=.25 or max(t)>=.5:return None
    for (u,v),w in zip(cyc,t):edges.append((u,v,w,'B'))
    w=np.array([e[2] for e in edges])
    B=np.zeros((6,len(edges)))
    for j,(u,v,_,_) in enumerate(edges):B[u,j]=w[j];B[v,j]=w[j]
    assert np.max(abs(B.sum(axis=1)-2))<1e-8
    ports=np.zeros((6,len(edges)),dtype=int)
    for j,(u,v,_,kind) in enumerate(edges):
        if kind=='H':ports[u,j]=0;ports[v,j]=0
        elif kind=='B':ports[u,j]=1;ports[v,j]=1
        else:ports[u,j]=0;ports[v,j]=1
    return edges,w,B,ports


def phase_max(w,edges,ports):
    best=0
    for bits in itertools.product([0,1],repeat=6):
        val=sum(w[j] for j,(u,v,_,_) in enumerate(edges) if bits[u]==ports[u,j] and bits[v]==ports[v,j])
        best=max(best,val)
    return best


def integer_max(w,B,q):
    sol=milp(-q,integrality=np.ones(len(w)),bounds=Bounds(np.zeros(len(w)),np.floor(1/w)),
             constraints=LinearConstraint(B,-np.inf,np.ones(6)),options={'time_limit':3,'mip_rel_gap':1e-8})
    return -sol.fun if sol.status==0 else None


def polar(w,B,limit=160):
    E=len(w);pats=np.eye(E)
    from scipy.optimize import linprog
    for it in range(limit):
        lp=linprog(-np.ones(E)/2,A_ub=pats,b_ub=np.ones(len(pats)),bounds=[(0,None)]*E)
        if lp.status:return None,it
        q=lp.x
        sol=milp(-q,integrality=np.ones(E),bounds=Bounds(np.zeros(E),np.floor(1/w)),
                 constraints=LinearConstraint(B,-np.inf,np.ones(6)),options={'time_limit':5,'mip_rel_gap':1e-8})
        if sol.status:return None,it
        if -sol.fun<=1+1e-7:return -lp.fun,it
        pats=np.vstack((pats,np.rint(sol.x)))
    return None,limit


def has_two_coloring(w,B):
    E=len(w);A=[];lb=[];ub=[]
    for j in range(E):
        row=np.zeros(2*E);row[j]=row[E+j]=1
        A.append(row);lb.append(1);ub.append(1)
    for c in range(2):
        for v in range(6):
            row=np.zeros(2*E);row[c*E:(c+1)*E]=B[v]
            A.append(row);lb.append(-np.inf);ub.append(1)
    sol=milp(np.zeros(2*E),integrality=np.ones(2*E),bounds=Bounds(np.zeros(2*E),np.ones(2*E)),
             constraints=LinearConstraint(np.array(A),lb,ub),options={'time_limit':3})
    return sol.status==0


if __name__=='__main__':
    import argparse
    ap=argparse.ArgumentParser();ap.add_argument('--asymmetric',action='store_true');ap.add_argument('--noncolor',action='store_true');args=ap.parse_args()
    cases=[]
    for s in [(0.27,.30,.33),(.26,.30,.34),(.28,.31,.34),(.28,.30,.32)]:
        for pl in itertools.permutations(range(3)):
            for pr in itertools.permutations(range(3)):
                for t0 in np.arange(.255,.46,.005):
                    ans=make(s,pl,pr,t0)
                    if ans is None:continue
                    if args.asymmetric and pl==pr:continue
                    edges,w,B,ports=ans
                    phase=phase_max(w,edges,ports)
                    cases.append((phase,s,pl,pr,t0,edges,w,B,ports))
    cases.sort(key=lambda a:a[0])
    print('admissible',len(cases),'best phase',cases[0][0],flush=True)
    shown=0;seen=set()
    for phase,s,pl,pr,t0,edges,w,B,ports in cases:
        if args.noncolor:
            key=(s,pl,pr)
            if key in seen:continue
            seen.add(key)
            if has_two_coloring(w,B):continue
        val=integer_max(w,B,w)
        rat,it=polar(w,B)
        print('phase',round(phase,5),'weight max',val,'polar',rat,'iters',it,'s',s,'pl',pl,'pr',pr,'t0',round(t0,4),flush=True)
        shown+=1
        if shown>=12:break
