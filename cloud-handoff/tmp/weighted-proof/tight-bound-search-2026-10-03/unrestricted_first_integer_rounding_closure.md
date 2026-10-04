# First integer-rounding cuts for arbitrary edge weights

This note proves a structural statement for all weights in `(0,1]`. It does
not prove a coloring bound. The distinction between repeatable edge types
and nonrepeatable physical edges is essential.

## Definitions

Let `E` be a finite collection of edge types on a finite loopless
multigraph. Different types may have the same endpoints and weight.
Type `e` has weight `w_e in (0,1]`. A color pattern is a vector
`z in Z_{≥0}^E` satisfying

    sum_{e incident v} w_e z_e <= 1       for every vertex v.

There is no upper bound of one on `z_e`: several copies of one type may
occur in a pattern. Let `P_global` be the convex hull of these patterns.
Let `P_local` require, at each vertex separately, membership in the convex
hull of that vertex's feasible integer count vectors.

Both polytopes are compact and downward closed. Their integer points are
the same. For any integral vector `p`, put

    L(p) = max_{x in P_local} p*x,
    M(p) = max_{z a global pattern} p*z.

The first integer-rounding closure, also called the first
Chvatal--Gomory closure, imposes every inequality

    p*x <= floor(L(p)),               p in Z^E.

Denote this closure by `CG(P_local)`.

## Theorem

For arbitrary weights in `(0,1]`,

    (2/3) P_local is contained in CG(P_local).

If the graph is bipartite, the stronger statement holds:

    (3/4) P_local is contained in CG(P_local).

The general factor `2/3` is best possible for this closure: three
unit-weight edge types on a triangle have local point `(1/2,1/2,1/2)`
and the rounded inequality `x_1+x_2+x_3 <= 1`.

## Reduction to nonnegative integral profits

Write `p+` for the coordinatewise positive part of `p`. Downward closure
gives `L(p)=L(p+)`: zeroing all coordinates with negative profit preserves
local feasibility. For every nonnegative `y`, `p*y<=p+*y`. It therefore
suffices to prove the rounded inequalities for integral `p>=0`.

Zero-profit types can also be deleted. This does not change either support
value: the projection of a local configuration hull onto the retained
types is precisely the local configuration hull after deletion. One
direction follows by deleting items from each bin, and the other by
inserting zero counts in the deleted coordinates.

For nonzero `p>=0`, at least one single-edge pattern has positive integral
profit. Thus `1<=M(p)<=L(p)`.

## General graphs

We first show

    M(p)=1 implies L(p)<=3/2.                         (1)

Every positive-profit type then has profit one. It has weight greater
than `1/2`, since otherwise two copies of it give profit at least two.
Any two positive-profit types intersect, since disjoint types can be
selected together. A pairwise intersecting loopless multigraph is a star
or has all its edges in one triangle. To see this, take intersecting
edges `uv,uw`. If an edge misses `u`, it must be `vw`; every edge meeting
all three of `uv,uw,vw` lies in that triangle. The case of only one
endpoint pair is already a star.

All retained types are heavy, so the local constraints are ordinary
matching degree constraints. They bound total count by one in a star
and by `3/2` in a triangle. This proves (1).

If `1<=L(p)<2`, integrality gives `M(p)=1`, so (1) yields
`(2/3)L(p)<=1=floor(L(p))`. If `L(p)>=2`, put `k=floor(L(p))>=2`.
Then `(2/3)L(p)<(2/3)(k+1)<=k`, unless `L(p)` is itself an integer,
in which case the desired inequality is immediate. Therefore every
point of `(2/3)P_local` satisfies every first rounded cut.

## Bipartite graphs: the low-profit step

If `M(p)=1`, the same reasoning gives a star, since a bipartite graph
has no triangle. Hence `L(p)=1`.

Suppose `M(p)<=2`. Every positive-profit type has weight greater than
`1/3`: three copies of any lighter type would give profit at least three.
Thus, after deleting zero-profit types, the problem has at most two
items per local bin. We now prove

    M(p)<=2 implies L(p)<=5/2.                        (2)

If every retained type has weight greater than `1/2`, the local
polytope is the bipartite matching polytope, so `L(p)=M(p)<=2`.
Otherwise choose a small positive-profit type `uv`, of weight at most
`1/2`. Its profit is one, since two copies fit. Every other positive
type meets `uv`, since two copies plus a disjoint edge would have profit
at least three.

If this support is a star, the local and global optima agree. Otherwise
both endpoints have side edges: let `A` be the types incident to `u`
but not `v`, and `B` those incident to `v` but not `u`. Bipartiteness
makes every `A` edge disjoint from every `B` edge. Consequently every
side type is heavy and has profit one; a small side type could be doubled
and combined with the opposite side, and a side type with profit at
least two could be combined with the opposite side.

All small types are therefore central, between `u` and `v`; call their
set `C`. Their profits are one. After swapping endpoints if necessary,
the minimum weight in `A` is at least the minimum weight in `B`. Every
type in `C` is incompatible with every type in `A`. Indeed, compatibility
with any member of `A` implies compatibility with the minimum-weight
members of both `A` and `B`, producing a feasible profit-three pattern.

The central heavy types have profit one or two. For any local point,
write `a,b,c,t,q` for the total counts of `A,B,C`, profit-one central
heavies, and profit-two central heavies. A profit-two central heavy
cannot share a local bin with any positive type: another heavy never
fits, and a compatible small would yield global profit three.

At either endpoint, bins containing a profit-two central heavy have
total probability `q`. The remaining bins imply

    a+c/2 <= 1-q,
    b+c+t <= 2(1-q),
    b+t <= 1-q.

Adding the first inequality and half of each other inequality gives

    a+b+c+t+2q <= (5/2)(1-q)+2q <= 5/2.

This proves (2) for arbitrary original weights.

## Bipartite graphs: all first rounded cuts

If `floor(L(p))=1`, then `M(p)=1`, so `L(p)=1`. If the floor is two,
then `M(p)<=2`, so (2) gives `(3/4)L(p)<=15/8<2`. For floor `k>=3`,
`(3/4)L(p)<(3/4)(k+1)<=k`, with integral endpoints immediate. This proves
the bipartite containment.

## What this does and does not establish

The earlier bipartite proof assumed every weight exceeded `1/3`.
That assumption is unnecessary: it follows automatically on the
positive-profit support in the only exceptional case of the rounding
argument. The theorem therefore treats all weights and arbitrary
parallel types.

Membership in the first closure does not imply membership in
`P_global`. Further integer-rounding cuts, or other global inequalities,
may separate the scaled local point. Accordingly neither
`chi'_w <= (4/3+o(1)) bp` for bipartite multigraphs nor
`chi'_w <= (3/2+o(1)) bp` for general multigraphs follows from this note.
Uniform conversion to physical integer edge colorings is another
requirement even after the global hull inclusion is proved.

The extension to arbitrary weights was independently checked by the
bipartite proof agent on 2026-10-03. No manuscript or repository theorem
was changed.
