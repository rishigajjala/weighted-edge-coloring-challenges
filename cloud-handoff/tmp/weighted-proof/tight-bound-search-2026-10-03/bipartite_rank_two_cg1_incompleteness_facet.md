# First CG closure is incomplete on every sufficiently long graded path

This corrects a tempting shortcut for a rank-two `4/3` proof. Although
`(3/4) P_loc` lies in the first Chvátal–Gomory closure, that closure is
strictly larger than the global configuration hull, even on a bipartite
tree with all weights above `1/3`.

Use the graded guard path of `../lower-bound-four-thirds.md` with
`m>=4`. Its `2m+1` edge types are `P_0,...,P_(m-1),H_0,...,H_m`.
Let `P_glob` be the convex hull of feasible one-color count vectors,
and `P_loc` the intersection of exact local configuration hulls. The
known injection proof gives the valid global inequality

    sum_i P_i + sum_j H_j <= m+1.                    (1)

It is a facet for every `m`. Let `A` contain one edge from every guard
bundle and none from any path bundle. For each `i=0,...,m-1`, let
`B_i` replace `H_(i+1)` by one `P_i`, and let `C_i` replace `H_i` and
`H_(i+1)` by two `P_i`. These `1+2m` patterns are feasible and tight in
(1): `H_i+P_i` fits, `2P_i` fits, and all other guards are disjoint
from the selected path edges.

They are affinely independent. In a linear dependence among their
differences from `A`, write coefficients `a_i` on `B_i-A` and `b_i` on
`C_i-A`. The `P_i` coordinates give `a_i=-2b_i`. The `H_0` coordinate
gives `b_0=0`; successively the `H_j` coordinates give
`b_j=b_(j-1)=0`. Hence all coefficients vanish. `P_glob` is
full-dimensional because zero and every unit vector are feasible, so
(1) is a facet.

For `m=4`, the nine patterns above, written as
`P_0...P_3 | H_0...H_4`, are:

    0000 | 11111
    0001 | 11110
    0002 | 11100
    0010 | 11101
    0020 | 11001
    0100 | 11011
    0200 | 10011
    1000 | 10111
    2000 | 00111

The augmented 9-by-9 matrix of these rows using columns
`(1,P_0,P_1,P_2,P_3,H_0,H_1,H_2,H_3)` has determinant `1`.

The vector `x_e=2/3` for every edge type belongs to `P_loc`. At each
internal vertex, pair the `2/3` mass of its outgoing path type with its
guard type, and pack the `2/3` incoming path mass in `1/3` bin. The
endpoints have the analogous pairing. Consequently the local support
value in the all-ones direction satisfies
`beta(1)>=(4m+2)/3>=m+2`, while every global color has at most `m+1`
edges.

For an integer-normal CG cut with normal `k*1` (`k` a positive integer),
the first-round right side is `floor(beta(k*1))>=k(m+2)`, so no such
cut supports facet (1). No original local inequality supports it
either.
If the first CG closure equaled `P_glob`, a finite facet description of
the rational CG closure would need an active inequality parallel to
(1) at a relative-interior point of this facet, a contradiction.
Therefore `CG_1(P_loc)` strictly contains `P_glob`.

This does not refute `(3/4) P_loc subseteq P_glob`; it only rules out
deducing that inclusion from first-CG containment plus completeness.
