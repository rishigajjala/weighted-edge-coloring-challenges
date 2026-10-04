# Opposite-shore capacity sensitivity for bipartite fluid matching

**Status (2026-10-03, within the required five-hour exploration interval):** verified auxiliary lemma, not a mixed-hull bound by itself. Fluid edges are uncapped and divisible; profits are nonnegative. The proof permits parallel edges.

For a bipartite fluid graph and `q>=0`, let

`F_q(r)=max{q·y : y>=0, Σ_{e∋v}y_e<=r_v for all v}`,

where `0<=r<=1`. Put `K=F_q(1)`, the maximum-weight ordinary fluid matching value under unit vertex capacities. If `u,v` lie on **opposite** shores and `r'=r+a e_u+b e_v<=1` with `0<=a,b<=δ`, then

`0 <= F_q(r')−F_q(r) <= δ K`.  (1)

**Proof.** Take an optimal flow `y'` under `r'`; because `r'<=1`, it is in the ordinary bipartite matching polytope. There is a matching decomposition of `y'` in which the events that `u` and `v` are **unmatched** are nested. To see this, let their matching degrees in `y'` be `d_u,d_v`, add an auxiliary edge `uv` with value `s=min(1−d_u,1−d_v)`, decompose the augmented fractional matching into integral matchings, and forget the auxiliary edge. The auxiliary event certifies joint unmatched status of probability at least `s`, which is its maximum possible value, so the two unmatched events, and equivalently the two matched events, are nested.

Let `a_0=(deg_{y'}(u)−r_u)_+<=a` and `b_0=(deg_{y'}(v)−r_v)_+<=b`. In the nested matching law, choose a set of state-time mass at most `max(a_0,b_0)<=δ`, and within it remove the selected edge at `u` in exactly mass `a_0` of states and the selected edge at `v` in exactly mass `b_0` of states. This is possible because their matched events are nested: select the smaller required mass inside the common matched event and extend only the larger side as needed. Each state loses a subset of one matching, so its lost profit is at most `K`. The resulting averaged flow has all former vertex degrees no larger than before and has degrees at `u,v` at most `r_u,r_v`; hence it is feasible under `r`. It loses profit at most `δK`, proving (1).

This has a direct concave-Jensen consequence. For `r^0<=r^1<=1` differing only by equal increases `h` at opposite-shore `u,v`, define `g(t)=F_q(r^0+t h(e_u+e_v))`, `t∈[0,1]`. Concavity of `F_q` in `r` makes `g` concave; monotonicity and (1) make it nondecreasing and `hK`-Lipschitz. For a Bernoulli state `B` of mean `p`, the chord deficit obeys

`g(p)−[(1−p)g(0)+p g(1)] <= p(1−p) hK <= K/4`.  (2)

Indeed `g(p)−g(0)<=phK`, while `g(1)−g(p)>=0`; the maximum deficit subject to nondecreasing `hK`-Lipschitz behavior occurs when all increase is before `p`, giving `(1−p)phK`. This is the favorable odd alternating-path case when every heavy edge has the same weight `h`: its two endpoint coverage statuses toggle together, so their residual capacities rise together on opposite shores, while all internal alternating-path vertex loads remain constant.

There is also a shorter independent dual proof of (1). In the vertex-cover dual for `F_q(r)`, choose an optimal nonnegative price vector `π` so that every positive coordinate has some tight incident edge: decrease slack positive coordinates until this holds, which cannot increase the objective. For opposite-shore `u,v`, one has `π_u+π_v<=K`. If either price is zero, the other's tight edge has profit at least that price, and `K` includes that edge. If both are positive and `uv` is tight, their sum is `q_uv<=K`. Otherwise choose a tight edge at each endpoint; these two edges are disjoint because `u,v` are on opposite shores and neither is `uv`, so their combined profit is at most `K` and at least `π_u+π_v`. Evaluate this same dual at the larger capacities to get `F_q(r')<=F_q(r)+aπ_u+bπ_v<=F_q(r)+δK`.

## Same-shore swap: a dual slope-range argument

The even alternating-path case also has a `K/4` chord bound, by a different argument. Let `u,v` lie on the same shore, say the left, and define

`g(t)=F_q(r^base+h[t e_u+(1−t)e_v])`, `0<=t<=1`,

with every displayed capacity at most one. The fluid vertex-cover dual is

`F_q(r)=min{Σ_i r_i π_i : π_i>=0, π_i+π_j>=q_ij for each fluid edge ij}`.

For any fixed right-shore dual prices `π_j`, choose every left price minimally:

`π_i=max_j (q_ij−π_j)_+`, taking missing edge profits as zero.

This preserves feasibility and cannot raise the dual objective. Put

`A=max_j(q_uj−q_vj)_+`, `B=max_j(q_vj−q_uj)_+`.

The elementary `max` comparison gives `−B<=π_u−π_v<=A` for every such minimal dual vector. If both `A,B` are positive, their maximizing right neighbors `j,k` are distinct. Hence fluid edges `uj` and `vk` form a matching and

`A+B <= q_uj+q_vk <= K`.

If one of `A,B` is zero, the other is at most the profit of a single fluid edge, hence at most `K`. Thus `A+B<=K` in all cases. Since `g` is the pointwise minimum of dual affine functions, all its one-sided slopes lie in `[−hB,hA]`. For a Bernoulli endpoint parameter of mean `p`, the chord deficit is bounded by

`g(p)−[(1−p)g(0)+p g(1)] <= p(1−p)h(A+B) <= K/4`.  (3)

The first bound follows from `g(p)−g(0)<=phA` and `g(p)−g(1)<=(1−p)hB`, multiplying by `1−p` and `p` respectively. This proof uses uncapped fluid edges: the two edges realizing `A,B` must both be selectable at their full unit amounts in the all-capacities-one benchmark `K`.

## Scoped mixed-hull consequence

Consider one mixed-local extreme point in a bipartite combined graph. Assume its positive-fluid support is a single tree, all heavy edges have the same weight `h∈[1/2,1]`, and the heavy marginal lies on a one-dimensional face of the bipartite heavy-matching polytope. Its two endpoint heavy matchings differ along one alternating path or even cycle. A cycle changes no vertex heavy degree, hence no weighted load at all, and cannot occur in a mixed-local extreme with a positive fluid tree: the face direction could be offset while preserving all active load rows. On a path, every internal vertex is covered in both endpoint matchings; only its endpoints vary. Odd path length toggles opposite-shore endpoints together, covered by (2). Even path length toggles same-shore endpoints oppositely, covered by (3). A path endpoint outside the fluid support simply contributes no recourse variation and gives the one-coordinate version of the same bound.

Consequently, for every nonnegative profit vector `q` on the positive-fluid tree, the full two-matching heavy law has fluid recourse at least `F_q(D)−K/4`, where `D_v=1−h Σ_{h'∋v}x_{h'}` is the mean residual. Mix this law with the empty heavy matching with probabilities `4/5` and `1/5`; the resulting heavy marginals are `(4/5)x`, and expected recourse is at least `(4/5)F_q(D)>=(4/5)q·y`. For each `q`, support-function separation supplies a joint state law with exact fluid mean `(4/5)y`. This is an **interim scoped transfer for one-fluid-tree extreme points with common heavy weight**, not a proof for multiple fluid components or heterogeneous heavy weights. The user's five-hour exploration interval is still in progress.
