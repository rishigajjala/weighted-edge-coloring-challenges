# All mixed row-sum blossoms survive 3/4 scaling on bipartite rank-two supports

**Research note.** This proves a necessary family of global inequalities,
not the full `3/4 P_loc subseteq P_glob` statement.

Let `G` be a loopless bipartite multigraph whose edge weights exceed
`1/3`. Let `P_loc` be the intersection of the exact local rank-two
configuration hulls described in
`../local-two-item-configuration-polytope.md`. Choose `x in P_loc`
and put `y=3x/4`.

At each vertex `v` in any vertex set `U`, choose one valid local row

    sum_(e incident to v) a_(v,e) x_e <= b_v,

where `b_v` is `1` for the heavy row and `2` for the total or a nested
threshold row. Coefficients lie in `{0,1,2}`. The mixed rounded row-sum
blossom is

    sum_(e=uv in E(U)) floor((a_(u,e)+a_(v,e))/2) y_e
      <= floor((sum_(v in U)b_v)/2).                 (★)

This is valid for every integral global rank-two pattern; the earlier
`rank-two-threshold-atom-hull-and-mixed-blossoms.md` introduces it.
Here it automatically holds for `y=3x/4`.

Put `T=sum_(v in U)b_v`. Summing the selected local rows over `U`,
discarding nonnegative boundary contributions, gives

    sum_(e=uv in E(U)) (a_(u,e)+a_(v,e))x_e <= T.

Therefore the left side of (★) is at most `3T/8`. For `T=0,1`, it is
zero because fewer than two vertices can be present; for `T=2` it is
at most `3/4<=1`; and for every integer `T>=4`,

    3T/8 <= floor(T/2).

The sole arithmetic exception is `T=3`, whose right side is one.
There are only two row patterns:

1. Three vertices all use the heavy row. Every internal edge counted
   on the left is heavy. Since a bipartite graph induced on three
   vertices is a star (allowing parallel edges), all counted edges
   meet one center vertex. Its heavy row bounds their total `x`-mass
   by one, so their `y`-mass is at most `3/4`.
2. Two vertices use one heavy row and one row of right side two. An
   internal small edge receives coefficient zero after the floor,
   while each internal heavy edge receives coefficient one. The heavy
   row bounds the total `x`-mass of these parallel heavy edges by one,
   again giving `y`-mass at most `3/4`.

Thus (★) holds in all cases.

The result exposes where a rank-two counterexample above `4/3`
would have to live: it cannot be separated from the local hull by one
of these mixed half-integral row-sum cuts. This does **not** establish
the inclusion, because completeness of the mixed blossoms for the
global configuration hull has not been proved; higher-rank or
non-row-sum facets may remain. The bipartite assumption is used only
in the three-heavy-row `T=3` case. A triangle of heavy edges makes that
case nonredundant on general supports.

## The blossom family is incomplete even for bipartite rank-two graphs

The exact `K4,4` instance in `bipartite_shared_guard_k44_exact_gap.md`
provides a counterexample to completeness. Give every one of its 16
edge types mean `x_e=1/2`. At each vertex the displayed two local
heavy-small pairs, each chosen with probability `1/2`, realize these
means in one bin. Thus `x in P_loc`.

The seven-type profit set

    {H_1,H_3,H_4,H_5,H_6,M_1,M_4}

has value `7/2` at `x`, whereas every integral global color pattern
has value at most three, as proved in that note. Hence `x` is outside
the global configuration hull. Nevertheless `x` satisfies **all**
mixed rounded row-sum blossoms: the standalone exact-integer checker
`verify_bipartite_k44_blossom_incomplete.py` enumerates all 312,500
choices of vertex subset and one heavy/total/prefix row per selected
vertex, with no violation.

This is a global cycle-coherence facet that cannot be recovered from
one round of these local row-sum cuts. It does not refute `3/4`
containment: the six-pattern coloring in the K4,4 note already puts
`6x/7` in the global hull, so certainly `3x/4` is in it. A universal
proof needs a bound on cycle-coherence cuts beyond the mixed blossoms.
