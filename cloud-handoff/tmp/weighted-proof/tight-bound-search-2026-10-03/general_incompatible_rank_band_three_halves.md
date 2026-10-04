# An exact 3/2 barrier for an incompatible heavy/rank-uniform mixture

**Scope.** This is a fixed-template, unbounded-count result for arbitrary
loopless multigraph support. Parallel types may have different weights and
profits. It does not prove a uniform integer-coloring bound over changing
templates.

Fix an integer `k>=2`. Every edge type is either heavy, with weight
`h>1/2`, or small, with weight `1/(k+1)<s<=1/k`. Assume every heavy and
small type that meet at a vertex are incompatible: `h+s>1`. Let `P_loc`
be the intersection of the exact one-bin integer-count hulls at all
vertices, and `P_global` the convex hull of globally feasible integer
count patterns. Counts can repeat a type up to its bin capacity.

**Theorem.** `(2/3) P_loc` is contained in `P_global`. Thus for every
nonnegative profit vector, the local-to-global support ratio is at most
`3/2`. The bound is sharp even if both classes occur with positive
multiplicity.

The same conclusion holds for **several small rank bands** under the
following exact local test. For each small type `e`, choose an integer
`k_e>=2` with `k_e w_e<=1`. Assume every feasible small-only bin `z` at
every vertex satisfies

    sum_(small e incident to v) z_e/k_e <= 1.            (R)

Retain the heavy-small incompatibility assumption. Then the exact local
hull is the simplex `H+sum_e x_e/k_e<=1`, because (R) puts every feasible
bin inside it and its axis vertices (one heavy copy or `k_e` copies of
one small type) are feasible. Set auxiliary `y_e=x_e` on heavy types and
`y_e=x_e/k_e` on small types. The matching argument below applies
word for word, expanding a selected small edge to `k_e` copies. This
is a directly checkable, multi-band sufficient condition.

For example, small weights `49/100` and `24/100` have ranks `2` and
`4`. In a feasible bin, the count `a` of `49/100` items is `0,1,2`;
the corresponding maximum count `b` of `24/100` items is `4,2,0`.
Thus `a/2+b/4<=1` in every case. Arbitrary mixtures of these two
weights satisfy (R), despite lying in different rank bands. Heavy
types of weight greater than `76/100` are incompatible with both.

There is also a quantitative form. Suppose every small-only feasible
bin has normalized rank sum at most `1+delta`, for a fixed `delta>=0`,
while heavy-small pairs remain incompatible. A local-law average then
satisfies

    H_v + sum_(small e incident to v) x_e/k_e <= 1+delta.

Apply the matching argument to `y/(1+delta)`. It gives the global mean
`(2/[3(1+delta)])x`, and hence the support gap bound
`3(1+delta)/2`. Thus a gap at least `3/2+epsilon` within this
incompatible-heavy model requires a feasible small-only bin with rank
sum at least `1+2epsilon/3` (or a limiting sequence approaching that
threshold). This is a necessary condition, not a sufficiency claim.

**Proof.** At a vertex, let `H` be the total heavy-type count and `S` the
total small-type count. Every feasible bin contains either one heavy
item or at most `k` small items. Conversely, every selection of at most
`k` small items fits, since each weighs at most `1/k`; no selection of
`k+1` fits, since each weighs strictly more than `1/(k+1)`. Hence the
exact local hull is

    H + S/k <= 1,       x >= 0.                         (1)

Sufficiency of (1) follows because its integer vertices are a heavy
singleton, `k` copies of one small type, and the origin. Equivalently,
it is the simplex whose axes have lengths one on heavy coordinates and
`k` on small coordinates.

For `x in P_loc`, form an auxiliary fractional edge vector `y` by
`y_e=x_e` on heavy types and `y_e=x_e/k` on small types. Equation (1)
gives `y(delta(v))<=1` at every vertex. The standard matching polytope
contains `(2/3)y`: degree inequalities are immediate, and for every odd
vertex set `U` of size at least three,

    (2/3)y(E(U)) <= |U|/3 <= (|U|-1)/2.

The first inequality follows by summing degree inequalities in `U`;
the second holds for odd `|U|>=3`. Decompose `(2/3)y` into a probability
law on ordinary matchings of auxiliary edge types. Expand a selected
heavy edge to one copy of its type and a selected small edge to `k`
copies. Each expanded matching is a globally feasible weighted count
pattern. Its mean on a heavy type is `(2/3)x_e`, and on a small type is
`k(2/3)(x_e/k)=(2/3)x_e`. This proves the inclusion.

**Sharpness with both classes present.** On a triangle take `N` heavy
items per side, all of weight `4/5`, and `M` small items per side, all
of weight `3/10` (`k=3`). The classes are incompatible. If `N` is even
and `M` is a multiple of twelve, the local bin number is exactly

    bp = 2N + 2M/3,

because each vertex has `2N` heavy items and `2M` small items, three
small items per bin. The heavy layer needs exactly `3N` colors. A
small-only color contains at most four items: its incident count at
each triangle vertex is at most three, so the sum over vertices bounds
the total by `floor(9/2)=4`. Exactly `3M/4` small colors suffice: use
the three rotations of the count pattern `(2,1,1)` equally often.
No color can mix heavy and small on the triangle, so

    chi'_w = 3N + 3M/4.

As `M/N` tends to zero through positive admissible values, the ratio
`chi'_w/bp` tends to `3/2`. The small class is present in every member.

**Interpretation.** This covers arbitrary graph topology and arbitrary
mixed weights within one small packing-rank band; condition (R) also
covers some mixed-band cases. A fixed-template count-hull construction
above `3/2` must therefore have either an incident heavy-small pair
that fits together or a feasible small-only bin whose normalized
rank sum exceeds one. The theorem rules out multiplication of a
heavy-triangle obstruction by merely overlaying small layers that
pass this local rank test.
