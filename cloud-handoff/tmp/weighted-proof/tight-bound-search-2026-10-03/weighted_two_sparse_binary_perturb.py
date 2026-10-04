"""Target L2-minimizer discrepancy >2 by perturbing binary tight cases."""
import json
import numpy as np


def sign_table(m):
    bits = ((np.arange(1 << (m-1))[:,None] >> np.arange(m-1)) & 1)
    return np.column_stack((np.ones(len(bits),dtype=np.int8),2*bits-1))


def main():
    rng=np.random.default_rng(31102027)
    tested=0
    boundary=0
    for n in range(4,8):
      for m in range(6,16):
        signs=sign_table(m)
        for rep in range(300):
          aa=np.zeros((n,m),dtype=np.int8)
          for e in range(m):
            u,v=rng.choice(n,size=2,replace=False)
            aa[u,e]=rng.integers(0,2)
            aa[v,e]=rng.integers(0,2)
            if aa[u,e]+aa[v,e]==0: aa[u,e]=1
          ss=signs@aa.T
          sq=np.sum(ss.astype(np.int64)**2,axis=1)
          mins=np.flatnonzero(sq==np.min(sq))
          tested+=1
          candidates=[]
          for i in mins:
            for v in range(n):
              if ss[i,v]!=2: continue
              plus=np.flatnonzero((signs[i]>0)&(aa[v]>0))
              minus=np.flatnonzero((signs[i]<0)&(aa[v]>0))
              if len(plus)>=3 and len(minus)>=1:
                candidates.append((i,v,int(minus[0])))
          if not candidates: continue
          boundary+=1
          for i,v,e in candidates[:6]:
            bb=aa.astype(np.int16)*10
            bb[v,e]=9
            tt=signs@bb.T
            tq=np.sum(tt.astype(np.int64)**2,axis=1)
            best=np.flatnonzero(tq==np.min(tq))
            bad=[j for j in best if np.max(np.abs(tt[j]))>20]
            if bad:
              j=bad[0]
              print(json.dumps({"tested":tested,"boundary":boundary,"n":n,"m":m,
                                "binary_matrix":aa.tolist(),"perturbed_matrix_tenths":bb.tolist(),
                                "sign":signs[j].tolist(),"sum_tenths":tt[j].tolist(),
                                "minimum_sq":int(tq[j]),"all_minimizers":len(best)}),flush=True)
              return
        print("PROGRESS",n,m,tested,boundary,flush=True)
    print("NO_COUNTEREXAMPLE",tested,boundary,flush=True)

if __name__=='__main__':main()
