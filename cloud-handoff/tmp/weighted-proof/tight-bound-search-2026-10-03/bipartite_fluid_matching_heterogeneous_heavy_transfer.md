# Interim: bipartite fluid matching with arbitrary heterogeneous heavy support

Status: independently audited intermediate transfer theorem under the five-hour proof-audit instruction. It does not assert the unrestricted weighted-edge-coloring bounds.

## Statement

Let the combined multigraph be bipartite. Heavy edge types `h` have weights `w_h in [1/2,1]` and locally categorical marginals `x_h>=0`, with `sum_{h incident v}x_h<=1`. Fluid edges have no supply caps and locally feasible loads `y_e>=0`, with `sum_{h incident v}w_hx_h+sum_{e incident v}y_e<=1`. Suppose the fluid support is a **matching**. Then the target heavy marginals `(3/4)x_h` and fluid load means `(3/4)y_e` lie in the convex hull of one-color mixed states. Heavy support, parallel types, and weights are arbitrary subject to the stated bipartition and local constraints.

## A nested-coverage full heavy law for all fluid pairs at once

For each fluid edge `e=uv`, define unweighted heavy-free marginals `a_v=1−sum_{h incident v}x_h` and `b_e=min(a_u,a_v)`. Because fluid edges are disjoint, the fractional vector consisting of all heavy edges with coordinates `x_h` and all fluid matching edges with coordinates `b_e` obeys every ordinary vertex degree bound: at an endpoint `v` of `e`, heavy degree plus `b_e` is at most one. The combined graph is bipartite, so the ordinary matching polytope is integral. Decompose this fractional vector into ordinary matchings, then forget which fluid edges were selected. This gives a full heavy matching law with each heavy edge marginal `x_h` and, for every fluid edge `e=uv`,

`Pr(u and v both heavy-free) >= b_e = min(Pr(u heavy-free),Pr(v heavy-free))`.

The reverse inequality holds for every coupling, so equality holds. Accordingly the two heavy-coverage events at `u,v` are **nested**: at most one of the discordant states `(u covered,v free)` and `(u free,v covered)` has positive probability. The same single full heavy law has this property simultaneously for every fluid edge. This also follows for one marked pair by alternating-path uncrossing, but the augmented matching-polytope argument gives the simultaneous version directly.

## Scalar additive-gap lemma

Let `U,V` be the heavy loads at the endpoints of one fluid edge in that full heavy law. Each is either zero or lies in `[1/2,1]`, and their positivity supports are nested. Then

`E max(U,V) − max(EU,EV) <= 1/3`.  (1)

To prove this, interchange `U,V` if needed so `{V>0} subseteq {U>0}` and put `Z=U−V`. On the common-positive event, `Z in[-1/2,1/2]`; on the `U`-only event, `Z in[1/2,1]`; elsewhere `Z=0`. Thus the pointwise inequality `Z_+ + 2Z_- <=1` holds. Also

`E max(U,V) − max(EU,EV) = min(EZ_+,EZ_-)`.

Since `3 min(a,b)<=a+2b` for nonnegative `a,b`, (1) follows by expectation. The constant `1/3` is sharp for this scalar class: with probability `2/3`, take `(U,V)=(1/2,1)`, and with probability `1/3`, take `(1,0)`.

For a unit-profit fluid edge, conditional physical recourse is `H(M)=min(1−U,1−V)=1−max(U,V)`. Its local fractional optimum at residual means `D_u=1−EU,D_v=1−EV` is `F(D)=min(D_u,D_v)=1−max(EU,EV)`. Equation (1) gives `E H(M)>=F(D)−1/3`. Because the same heavy law makes every fluid pair nested, multiplying by arbitrary nonnegative profits `q_e` and summing over the disjoint fluid edges yields

`E F_q(r(M)) >= F_q(D) − (1/3)F_q(1)`.

Here `F_q(1)=sum_e q_e`, since the fluid support is a matching.

## Quarter empty-state mixture

Take the full heavy law above with probability `3/4` and the empty heavy matching with probability `1/4`. Every heavy edge now has exact marginal `(3/4)x_h`. Conditional fluid recourse is unrestricted under the empty heavy matching, and its value is `F_q(1)`. Therefore

`E F_q(r(M_new)) >= (3/4)[F_q(D)−F_q(1)/3]+(1/4)F_q(1) = (3/4)F_q(D) >=(3/4)q·y`.

This holds for each nonnegative `q` under a heavy law **independent of q**. The expected conditional fluid-feasible set is convex and downward closed; support-function separation gives conditional fluid allocations whose means are exactly `(3/4)y_e` while preserving all heavy marginals. The proof is for uncapped divisible fluid edges. It does not extend the scalar additive bound to fluid stars of arbitrary size: a heavy even cycle plus a many-leaf fluid star gives an unscaled additive gap of `1/2`.
