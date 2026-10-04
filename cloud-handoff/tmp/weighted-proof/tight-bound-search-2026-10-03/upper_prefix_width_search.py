"""Test whether a two-point packet coupling keeps every two-copy prefix width <=2.

This tests a sufficient condition for a half Jensen-gap bound, not the bound.
"""
import itertools
import random

import networkx as nx
import numpy as np
from scipy.optimize import linprog


def orders(n):
    for word in itertools.product(range(n), repeat=2*n):
        if all(word.count(i)==2 for i in range(n)) and tuple(dict.fromkeys(word)) == tuple(range(n)):
            yield word


def feasible(word, lo, hi, prob):
    n=len(lo)
    states=list(itertools.product((0,1), repeat=n))
    values=[]
    for s in states:
        counts=[0]*n
        row=[]
        for i in word:
            counts[i]+=1
            row.append(sum(counts[k]*(hi[k] if s[k] else lo[k]) for k in range(n)))
        values.append(row)
    g=nx.Graph()
    g.add_nodes_from(range(len(states)))
    for i,j in itertools.combinations(range(len(states)),2):
        if max(abs(a-b) for a,b in zip(values[i],values[j]))<=2+1e-9:
            g.add_edge(i,j)
    for clique in nx.find_cliques(g):
        mat=np.array([states[i] for i in clique],dtype=float).T
        eq=np.vstack((np.ones(len(clique)),mat))
        res=linprog(np.zeros(len(clique)),A_eq=eq,b_eq=[1,*prob],
                    bounds=(0,None),method='highs')
        if res.success:
            return True
    return False


if __name__=='__main__':
    rng=random.Random(20261003)
    grid=[0,.2,.4,.6,.8,1]
    for n,trials in [(3,20000),(4,30000)]:
        ww=list(orders(n))
        for t in range(trials):
            word=rng.choice(ww)
            ab=[tuple(sorted(rng.sample(grid,2))) for _ in range(n)]
            lo,hi=zip(*ab)
            prob=[rng.choice((.1,.2,.3,.4,.5,.6,.7,.8,.9)) for _ in range(n)]
            if not feasible(word,lo,hi,prob):
                print('FAIL',n,t,word,lo,hi,prob,flush=True)
                break
        else:
            print('PASS',n,trials,flush=True)
