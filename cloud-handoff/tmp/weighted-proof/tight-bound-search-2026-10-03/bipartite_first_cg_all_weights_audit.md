# First-CG scaling across all positive weights: scope audit

The `3/4` containment proved for bipartite rank-two types in
`bipartite_rank_two_first_cg_three_quarters.md` extends unchanged to
**all weights in `(0,1]`**, provided coordinates denote repeatable
edge types: a one-color configuration can include several copies of
the same type whenever their total weight fits.

For nonnegative integral profit `p`, let `beta=max_{x in P_loc}p·x`
and `M=max_{z in P_glob cap Z^E}p·z`. If `beta>=3`, elementary
arithmetic gives `(3/4)beta<=floor(beta)`. If `beta<3`, then the
integer `M<=2`. Any positive-profit type of weight `<=1/3` would
allow three copies of itself in one color, giving `M>=3` and a
contradiction. Delete zero-profit coordinates (downward closure makes
the local and global projections exact). Every remaining positive
type has weight `>1/3`, so the rank-two low-profit lemma gives
`beta<=5/2` if `M=2`, and `beta=1` if `M=1`. In both cases
`(3/4)beta<=floor(beta)`. Signed integer normals reduce to their
positive parts by downward closure. Hence on loopless bipartite
repeatable-type supports,

    (3/4) P_loc is contained in CG_1(P_loc)

for arbitrary positive weights.

On an arbitrary loopless multigraph, the same low-support argument
gives `(2/3)P_loc subseteq CG_1(P_loc)` for arbitrary weights. The
arithmetic is automatic for `beta>=2`. If `beta<2`, then `M<=1`.
Any positive type has weight `>1/2` (otherwise two copies give
profit at least two) and unit profit. Any two disjoint positive
types would also give profit two. A pairwise-intersecting loopless
multigraph support is a star or a triangle. A heavy star has local
profit at most one, and a heavy triangle has local fractional
matching profit at most `3/2`, exactly what the `2/3` scaling needs.

These assertions concern the repeatable-type asymptotic
configuration model. If coordinates instead distinguish individual
physical edge occurrences and a single occurrence cannot be repeated,
the 'three copies of a light type' inference does not apply as
stated. The type formulation is the one used in the weighted
configuration-gap program here.

First-round containment alone does not imply global-hull containment.
The argument controls potential cuts with integer support value at
most two; a higher-round cut of global profit at least three could
still separate `(3/4)P_loc`. Iterating the displayed containment
would compound the scale factor unless one proves the *same* scaled
local polytope survives every round.
