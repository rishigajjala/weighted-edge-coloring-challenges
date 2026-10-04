"""Exact integer audit: all mixed row-sum blossoms miss a K4,4 gap.

The normalized local point has x_e=1/2 for each of 16 edge types.
The seven-type global cut in bipartite_shared_guard_k44_exact_gap.md
separates it: 7/2>3. This script checks every choice of local rows and
vertex subset in the rank-two threshold row-sum blossom family.
"""
from itertools import product

HEAVY = [34,32,36,32,38,34,34,34]
SMALL = [22,28,26,26,24,26,22,26]
WEIGHTS = HEAVY + SMALL
EDGES = ([(i,4+i) for i in range(4)]
         + [(i,4+(i+1)%4) for i in range(4)]
         + [(i,4+(i+2)%4) for i in range(4)]
         + [(i,4+(i+3)%4) for i in range(4)])


def rows_at(v):
    ids = [i for i,e in enumerate(EDGES) if v in e]
    heavy = [i for i in ids if i < 8]
    small = [i for i in ids if i >= 8]
    rows = [('off', 0, [0]*16)]
    hrow = [0]*16
    for i in heavy:hrow[i] = 1
    rows.append(('heavy', 1, hrow))
    total = [0]*16
    for i in ids:total[i] = 1
    rows.append(('total', 2, total))
    for threshold in sorted(set(WEIGHTS[i] for i in heavy)):
        row = [0]*16
        for i in heavy:row[i] = 1 + int(WEIGHTS[i] >= threshold)
        for i in small:row[i] = int(WEIGHTS[i] > 60-threshold)
        rows.append((f'prefix{threshold}', 2, row))
    for name,b,row in rows:
        assert sum(row) <= 2*b  # x_i=1/2 satisfies this local row
    return rows


def main():
    rows = [rows_at(v) for v in range(8)]
    count = 0
    maximal_margin = -10**9
    maximal_choice = None
    for choice in product(*rows):
        count += 1
        total_rhs = sum(row[1] for row in choice)
        twice_left = sum((choice[u][2][i]+choice[v][2][i])//2
                         for i,(u,v) in enumerate(EDGES))
        twice_right = 2*(total_rhs//2)
        margin = twice_left-twice_right
        if margin > maximal_margin:
            maximal_margin = margin
            maximal_choice = tuple(row[0] for row in choice)
        assert margin <= 0, (choice, margin)
    assert count == 312500
    print({'row_choices_checked':count, 'max_twice_violation':maximal_margin,
           'example_tight_choice':maximal_choice,
           'global_separating_profit_types':(1,3,4,5,6,9,12),
           'global_profit_at_x':'7/2', 'global_profit_bound':3})


if __name__ == '__main__':main()
