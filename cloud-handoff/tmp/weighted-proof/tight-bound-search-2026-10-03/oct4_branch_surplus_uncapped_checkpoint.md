# Branching checkpoint: uncapped star surplus pays an arbitrary core in a dominant-spoke profit regime

4 October 2026. This is a restricted support-objective inequality and a
possible mechanism for gluing branches. It does **not** establish the
fixed-hybrid law for capped arbitrary-support fluid or unrestricted
profit vectors.
In particular, the positive baseline below disappears when the spoke
prefix is empty or its edges have caps below one.

## One unguarded center with positive uncapped spokes

Use unit-weight categorical heavy pairs with matching simple support
and the fixed heavy law: probability `3/4` independent pair states at
scaled marginals `2x/3`, probability `1/4` common-threshold pair
states at the same marginals. Let an unguarded center have a nonempty
set of positive-target fluid spokes of total target mass `s∈(0,1]`.
Assume each spoke can carry a full unit when its leaf and the center
are free (uncapped divisible flow). Group leaves that belong to one
heavy pair. If group `i` has target mass `Y_i`, local feasibility gives
the pessimistic pair-free probability `p_i=(1+Y_i)/3`; singleton or
unguarded groups have at least this much availability. We have
`ΣY_i=s`.

Let `m=max_i Y_i` and `P=∏_i(1−p_i)=∏_i(2−Y_i)/3`.
The expected optimal unit-profit spoke recourse is at least

`H(s)=(3/4)(1−P)+(1/4)(1+m)/3`.

If there is one group, `m=s` and `H(s)=(1+s)/3`. If there are at least
two, merge all groups except a largest one. The elementary inequality
`[(2−a)(2−b)]/9≤(2−a−b)/3` for `a+b≤1` shows that merging raises
the failure product, so

`P≤(2−m)(2−s+m)/9`.

Consequently

`12[H(s)−(1+s)/3]
 ≥6+m−4s−(2−m)(2−s+m)
 =2(1−s)+m(1−s)+m²≥0`.

Thus `H(s)≥(1+s)/3`, with equality for a single group. Relative to
the required scaled spoke target `2s/3`, this gives surplus at least
`(1−s)/3`. This stronger estimate uses uncapped *full-unit* recourse;
the audited cap-12 star theorem gives the required `2s/3` but does not
itself imply this precise surplus for all small `s`.

## Two interacting branch centers, one equal-profit bridge

Take two distinct unguarded centers `c,d`, each with a nonempty
positive-target spoke set of masses `s_c,s_d`, and join them by one
fluid bridge of target mass `a`. Assume the spoke supports are
vertex-disjoint, their leaves can supply one full unit when free, and
all these fluid edges have unit profit. Local feasibility gives
`s_c+a≤1` and `s_d+a≤1`. Ignore the bridge in the recourse pattern.
The two spoke stars can run simultaneously, even if a heavy pair links
one leaf of each star; their vertices are disjoint and expected profits
add. The preceding bound gives

`E F ≥ H(s_c)+H(s_d)
      ≥(2+s_c+s_d)/3
      ≥(2/3)(s_c+s_d+a)`,

where the last step is the sum of the two center constraints.
Thus the spokes' quantitative surplus pays the bridge's **unit-profit
support objective** without using the bridge. This does not imply its
coordinate marginal, nor an arbitrary-profit inequality: a high bridge
profit cannot be paid by lower-profit spokes. If either spoke set is
empty, the baseline `1/3` cannot be assigned to that center and the
argument must be replaced by actual bridge recourse.

## Arbitrary core graph and a weighted dominant-spoke condition

The preceding charge does not depend on the bridge being the only
core edge. Let `V_0` be any set of unguarded centers, each with a
nonempty **positive-profit** private spoke set of target mass `s_v>0`.
Assume spoke stars are vertex-disjoint, although heavy pairs may link
their leaves. Let an arbitrary fluid core graph on `V_0` have target
load `r_v` at center `v`. Local feasibility gives `s_v+r_v≤1`.
All spokes and core edges here have uncapped divisible-flow capacity.

If every edge has unit profit, ignore the core in the statewise
recourse. The spoke stars remain feasible simultaneously, and their
expected total profit is at least

`Σ_v (1+s_v)/3
 ≥ (2/3)[Σ_v s_v+Σ_{e in core}y_e]`,

because `2Σ_core y_e=Σ_v r_v≤|V_0|−Σ_v s_v`.
The core may have cycles, parallel edges, or unbounded degree.

For one arbitrary nonnegative profit vector `q`, there is a weighted
version. Suppose all positive-profit spokes at center `v` have profit
at least `a_v>0`, and every positive-profit core edge `uv` obeys

`q_uv≤(a_u+a_v)/2`.

Within one star and a fixed heavy state, let `F_{q_v}` be optimal
spoke recourse, `F_1` optimal unit-profit spoke throughput, and
`F_{q_v−a_v}` optimal recourse for the nonnegative extra profits.
The exact identity

`F_{q_v}=a_v F_1+F_{q_v−a_v}`

holds: an extra-profit-optimal flow can be extended to maximum total
star throughput without decreasing its extra profit. Indeed, after
any feasible partial flow, the remaining center capacity and each
leaf's remaining capacity/caps support exactly the unused portion
of the star's maximum total throughput. The audited uncapped star
transfer applied to the extra-profit vector and the lower bound
`E F_1≥(1+s_v)/3` therefore give

`E F_{q_v}≥(2/3)Σ_{e in spoke(v)}q_e y_e
             +a_v(1−s_v)/3`.

The second term pays the scaled core target, since

`(2/3)Σ_{uv in core}q_uv y_uv
 ≤(1/3)Σ_v a_v r_v
 ≤(1/3)Σ_v a_v(1−s_v)`.

Thus, for this specified `q`, the **spoke-only** recourse has expected
profit at least `(2/3)q·y` on the combined spoke/core target. This is
only a support inequality for profit vectors satisfying the displayed
core-price condition; it does not provide positive marginals on core
edges, and it cannot establish the full mixed hull for all `q` without
handling high-price core edges separately. A center whose selected
positive-profit spoke prefix is empty has no `a_v/3` baseline.

## Dual-price interface for an uncapped, q-optimal target

The weighted condition has a natural LP-dual interpretation. For the
uncapped local fluid degree polytope, a nonnegative profit vector `q`
has dual vertex prices `pi_v≥0` with `q_uv≤pi_u+pi_v`; at a q-optimal
target, every positive edge satisfies equality. If each positive
spoke `vℓ` in the above decomposition has
`pi_ℓ≥pi_v`, then
`q_vℓ=pi_v+pi_ℓ≥2pi_v`. Setting `a_v=2pi_v` makes every spoke meet
the lower profit requirement, while every core edge automatically
satisfies `q_uv≤pi_u+pi_v=(a_u+a_v)/2`. A positive-price center must
still have a nonempty positive spoke set to earn its baseline;
zero-price centers can take `a_v=0` and need no baseline.

This is an **interface**, not an orientation theorem. An arbitrary
fluid forest need not admit a decomposition into vertex-disjoint
private-leaf stars plus a core on their unguarded centers with every
spoke pointing from lower to higher dual price. A vertex can be a leaf
of one favorable edge and the center of another. Also, for the
`C_e≥12y_e` capped transfer, a fixed target `y` need not be q-optimal
in the uncapped local degree polytope; replacing it by a q-optimal
target may violate the original caps. Complementary equality on
positive spokes cannot be assumed in that setting without another
decomposition or slack argument.

Even in the uncapped q-optimal setting, a favorable private-star/core
decomposition need not exist. Take the four-vertex fluid path
`1–2–3–4` with edge profits `(3,6,7)`, target `y_e=1/5` on each
edge, and local allowances `(D_1,D_2,D_3,D_4)=(1/5,2/5,2/5,1/5)`.
The target is q-optimal: `pi=(1,2,4,3)` is a nonnegative dual with
every positive edge tight and primal/dual value `16/5`. The D values
are also compatible with unit-heavy matching pairs `(1,4)` and
`(2,3)`. Any disjoint private-star plus center-core decomposition of
all three path edges needs centers `2,3`, private spokes `1–2,3–4`,
and core edge `2–3`. Every tight dual has the form
`pi=(t,3−t,3+t,4−t)`. Favorability of both spokes would require
`t≥3/2` and `t≤1/2` simultaneously. Thus this dual-oriented
decomposition fails even though the separate max-degree-two transfer
theorem handles the path. A broader proof must allow price-unfavorable
spokes or use another mechanism on the core.

## Why a plain leaf induction does not suffice

The exact star counterexample in
`oct4_paired_leaf_naive_induction_counterexample.md` shows that
full-minus-reduced recourse can be less than the removed leaf's scaled
target even with caps `C≥12y`. The full theorem survives because the
reduced instance has a large surplus. Any general forest argument
based on deletion therefore needs a quantitative surplus invariant
or grouped paired-source elimination. The displayed uncapped estimate
is one such surplus, but it has not been extended to the capped,
weighted, interacting-branch setting.
