# The 3/4-scaled bipartite rank-two local hull survives every first CG cut

**Research note.** All edge weights lie in `(1/3,1]`. This establishes
membership in the first Chvátal–Gomory closure of the local
configuration polytope, not in the global integer configuration hull.

Let `P_loc` be the intersection of the exact local repeatable-count
configuration hulls of a loopless bipartite multigraph. Let `P_glob`
be the convex hull of globally feasible integer count patterns. For a
nonnegative integer profit vector `p`, define

    L(p)=max{p·x : x in P_loc},
    M(p)=max{p·z : z an integral global color pattern}.

The key low-profit lemma is

    M(p)<=2  ==>  L(p)<=5/2.                       (1)

If `M(p)=1`, in fact `L(p)=1`.

## Proof of the low-profit lemma

If no positive-profit edge is small (`w<=1/2`), the positive support
consists entirely of heavy edges. Its local projection is the ordinary
bipartite matching polytope (`sum incident x_e<=1` at every vertex),
which is integral. Therefore `L(p)=M(p)<=2`.

Suppose a positive small edge `e=uv` exists. Its profit is one: two
copies of `e` fit in a color, so profit at least two is forced, and
profit two on `e` would give a color of profit four. Moreover every
other positive edge meets `e`; otherwise two copies of `e` together
with one disjoint positive edge would have profit at least three.
Thus the positive support is covered by `u,v`.

If all positive edges meet one common vertex, the global and local
profit maxima coincide: every feasible configuration at that center
is feasible on its star globally. So assume the positive support is
not a star. There are positive side edges from `u` to other vertices
and from `v` to other vertices. Any other positive small edge must be
parallel to `e`: if it were a side edge, it would be disjoint from a
positive edge on the opposite side, and its two copies together with
that edge would have profit three. Hence all positive side edges are
heavy. Their profits are one, since a side edge of profit at least two
could be combined with a disjoint positive edge on the opposite side.
All positive central small edges have profit one.

Let `A` and `B` denote the heavy side edges at `u` and `v`, and `C`
the central small edges. Every `c in C` is incompatible with **all**
edges on one fixed side. To see this, let `alpha` and `beta` be the
minimum weights among `A` and `B`. If, say, `alpha>=beta` and a `c`
fit any edge of `A`, it would fit an edge of weight `alpha` and also
one of weight `beta`. These two side edges are disjoint and, together
with `c`, would make a feasible profit-three pattern. Thus every `c`
rejects every edge of `A`. Swap sides if necessary.

Central heavy positive edges may have profit one or two. Write `a,b,c,t,q`
for the total local means of `A,B,C`, central heavy edges of profit
one, and central heavy edges of profit two, respectively. A profit-two
central heavy edge cannot coexist with any other positive edge: it
rejects other heavies automatically, and a compatible central small
edge would produce profit three. At either endpoint the probability
of a profit-two central heavy occurrence is exactly `q`, since at
most one heavy occurs in a bin. All other positive counts vanish in
those bins.

At `u`, no `A` edge can pair with a `C` edge, so every remaining local
bin satisfies `A+C/2<=1`. At `v`, a local bin has at most two of the
unit-profit items `B,C,t`, and at most one of the heavy items `B,t`.
Taking expectations only over bins without a profit-two central heavy
gives

    a+c/2 <= 1-q,
    b+c+t <= 2(1-q),
    b+t <= 1-q.

Add the first inequality to one half of each of the last two:

    a+b+c+t <= (5/2)(1-q).

Hence the total profit is

    a+b+c+t+2q <= 5/2-q/2 <=5/2,

proving (1). If `M(p)=1`, any two positive edges must intersect;
otherwise they form a feasible profit-two pattern. Pairwise
intersecting edges of a bipartite multigraph share a common vertex,
so the positive support is a star and `L(p)=M(p)=1`.

## Consequence for the first CG closure

For a nonnegative integer vector `p`, the strongest rank-one integer
rounding of its valid local inequality is

    p·z <= floor(L(p)).

Take any `x in P_loc` and set `y=3x/4`. If `L(p)>=3`, then
`(3/4)L(p)<=floor(L(p))`: this follows by checking each interval
`[k,k+1)` for integer `k>=3`. If `1<=L(p)<3`, then the integral
global maximum is at most two; (1) gives `L(p)<=5/2`, and therefore
`p·y<=15/8<2<=floor(L(p))` when the floor is two. When the floor is
one, the `M(p)=1` part of the lemma gives `L(p)=1`, so the cut also
holds. The zero-profit case is trivial.

Signed integer normals do not add a threat for nonnegative `y`:
downward closure of `P_loc` makes the local support function of a
signed normal equal to that of its positive part, while the signed
left side at `y` is no larger. Therefore

    (3/4) P_loc is contained in the first CG closure of P_loc.

This is strictly weaker than `(3/4)P_loc subseteq P_glob`. The exact
`K4,4` example in `bipartite_shared_guard_k44_exact_gap.md` has a
first-round coherence cut not present in the narrower mixed
half-row-sum blossom family; higher-round cuts may still be needed in
other examples. No unrestricted `4/3` coloring theorem follows here.
