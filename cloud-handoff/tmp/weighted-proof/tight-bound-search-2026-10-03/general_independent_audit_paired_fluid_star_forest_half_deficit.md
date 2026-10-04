# Independent audit of the paired fluid-star-forest half deficit

This checks `upper_arbitrary_paired_star_forest_half_deficit.md` as saved
on 3 October 2026. **Verdict: the stated divisible-fluid 3/2
configuration theorem is valid under its model.** The proof gives no
integer weighted-edge-coloring conclusion for arbitrary indivisible
edges.

## Scalar lemma

For arbitrary real `z_i in [0,1]`, the pointwise inequality

    (sum_i z_i-1)_+ <= sum_(i<j) z_i z_j                 (A)

is valid. Induct on the number of summands. If the old sum `s>=1`,
adding `z` raises the left side by `z`, while the new pair terms add
`zs>=z`. If `s<1<s+z`, the rise `s+z-1` is at most `zs` because
`(1-s)(1-z)>=0`. Otherwise the rise is zero. Independence therefore
gives `E(sum Z_i-1)_+<=m^2/2` when the mean sum `m<=1`; binary
summands are not required.

For one private `Y in [0,2]`, the minimum overflow transport cost is
convex in its law: mixing couplings for two laws gives a coupling of
their mixture at the mixed cost. On a finite grid, the fixed-mean
probability polytope has extreme laws supported on at most two points.
Randomized rounding of a general `Y` to adjacent grid points preserves
its mean and has Wasserstein-1 error at most the mesh; the minimum
cost is one-Lipschitz in that distance because the hinge is
one-Lipschitz in `Y`. Thus checking two-point laws is sufficient,
with the convexity direction correctly oriented.

Write such a law as `Y=a+dB`, `P(B=1)=p`, and set `U'=U+a`,
`m=E U'`. The mean constraint gives `m+pd<=1`, and `a<=1`, so the
constant `a` is a legitimate extra independent `[0,1]` summand.
If `d<=1`, make `B` independent and use (A). If `1<d<=2`, assign
`B=1` to the lowest `p` mass of `U'`, randomizing at an atom. This
gives `E[U'1_B]<=pm`. The overflow is bounded by

    E(U'-1)_+ + p(d-1) + E[U'1_B]
      <= m^2/2+p(d-1+m)
      <= 1/2+(1-m)^2(1/2-1/d) <=1/2.

The last inequality uses `p<= (1-m)/d` and `d<=2`. The bound is
valid for a constant `Y` too (`d=0`).

For several prescribed private variables `Y_i in [0,2]`, couple
their running sum oppositely by quantiles with the next variable.
Both input support widths are at most two; for two ordered quantile
positions, one summand increases and the other decreases, each by at
most two. Their sum's difference is therefore at most two in
absolute value. This maintains aggregate width at most two. Lift each
step via the preceding vector's conditional law given its sum, so all
private marginals remain exact. If the aggregate lower support endpoint
is `a`, then `a<=E sum_i Y_i<=1`; shifting `a` into `U` is valid.
The one-private-variable argument applies to the shifted aggregate,
and conditional lifting preserves the complete joint law of the
original independent base summands.

## Global coupling

Sample independently the discrete pairs whose endpoints do not both
lie in a single fluid-star component. In one star, their residuals
enter the preliminary singleton leaf flows from distinct pairs and
possibly the hub residual `X`; they are independent within this star,
even when a pair links two different stars. A pair with both endpoints
in the star is private to it. If its endpoints are two leaves, its
combined preliminary flow is `Y_i=(c_1+c_2)R_i in [0,2]`. If its
endpoints are the hub and one leaf, its leaf flow is `cX`, with
`0<=c<=1`, and no separate private variable is needed for it.

With `S` the sum of other singleton preliminary flows, the base

    U=1-(1-c)X+S

has independent `[0,1]` summands: the first is a function solely of
`X`, in `[c,1]`, and each flow in `S` comes from a distinct sampled
pair or fixed leaf. Hub mean feasibility is precisely
`E U+sum_i E Y_i<=1`. The scalar lemma bounds the expected hub
overload by `1/2`. Its coupling preserves the *joint* shared-source
law within the star. Given the globally sampled shared sources, draw
each star's private pair variables from its conditional kernel.
Private pair sets of distinct stars are disjoint, so all these kernels
can be applied simultaneously even when the star-incidence graph of
shared pairs has cycles. Packet identities can subsequently be drawn
from each pair's prescribed conditional packet law given its residual.

Proportional trimming at the hub removes exactly the positive hub
overload from its incident preliminary flows. Each leaf has only one
fluid edge, so its individual expected loss is at most the same
`1/2` bound. Thus the deficit vector `d=y-EY` is nonnegative and has
incident sum at most `1/2` at every vertex. The vector `2d` is an
all-capacity-one feasible divisible flow, proving profit loss at most
`A/2`. The `2/3` packet-rounding gate plus a `1/3` all-empty
discrete state cancels exactly that `A/2` loss and gives the
`3/2` support ratio.

The proof requires divisible fluid, a vertex-disjoint union of stars,
and discrete support consisting of disjoint pairs with equal residual
at the pair's two endpoints. It does not establish an unrestricted
weighted integer-coloring bound or any uniform rounding error.

## Audit of the later coordinatewise and bipartite amendments

The amended Section 3 gives an exact coordinatewise inclusion, not
only a support-function inequality. Given preliminary fluid mean `y`
and trimmed mean `t`, the deficit `d=y-t` is nonnegative and has
incident sum at most `1/2` everywhere. Therefore the deterministic
fluid flow `2d` is feasible at all-one capacities. Mixing the normal
packet/trimmed-flow state with probability `2/3` and the empty-packet
state carrying `2d` with probability `1/3` yields exactly
`(2x/3,2y/3)`. This uses divisible fluid and no per-edge supply cap
beyond vertex capacity.

If the combined discrete-plus-fluid support is bipartite, a discrete
pair cannot join two leaves of one fluid star: those two spokes and
the pair form a triangle. An internal pair can only join the hub to
one leaf. Sample all pair residuals independently, reserve this
possible own-pair leaf flow as `cX`, and write `H=(1-c)X`, while `S`
is the sum of other independent singleton leaf flows. Then `H` and
the summands of `S` are independent and in `[0,1]`, and mean hub
feasibility gives `mu=E S<=r=E H<=1`. The elementary independent
bound `E min(1,S)>=1-exp(-mu)` and the pointwise inequality
`min(H,S)>=H min(1,S)` imply

    E(S-H)_+ <= mu-r+r exp(-mu)
              <= mu exp(-mu) <=1/e.

Thus trimming creates incident deficit at most `1/e`, and the same
direct correction construction with normal probability
`alpha=e/(e+1)` and empty probability `1/(e+1)` uses flow
`e(y-t)` to realize exactly `(alpha x,alpha y)`. Shared discrete pairs
may link stars cyclically because their independently sampled laws
are globally consistent. The bipartite factor `1+1/e` is valid for
the entire stated mixed star-forest model.

The stated sharp general witness also checks: a unit discrete edge
`uv` plus unit-density fluid spokes `uz,vz` has a locally feasible
point of profit `3/2` and global maximum one. In the physical
approximation with even `B` and reciprocal-integer `epsilon`, local
packing is exactly `B`, while `B/2` discrete colors and `B` spoke
colors are both necessary and sufficient, so `chi'_w=3B/2`.
