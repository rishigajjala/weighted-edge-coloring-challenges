# Bipartite independent-heavy recourse: exact three-quarters theorem

Let `G=(L,R,E)` be a bipartite fluid graph with nonnegative edge profits `q`. For a vertex set `S`, let `m_q(S)` be the maximum weight matching in the induced graph `G[S]`. Unit binary vertex capacities make this equal to the fractional fluid recourse value. A heavy pair has one endpoint in `L` and one in `R` whenever the **combined** heavy-plus-fluid graph is bipartite.

## Opposite-side supermodularity

For `u in L`, `v in R`, and a fixed set `S` excluding both,

`m_q(S+u+v)+m_q(S) >= m_q(S+u)+m_q(S+v)`.

Take optimum matchings `M_u` and `M_v` for the two one-added graphs. If either added vertex is unmatched in its optimum, the inequality follows directly. Otherwise color `M_u` red and `M_v` blue, removing common edges temporarily. Their symmetric difference comprises alternating paths and cycles. Vertex `u` is an endpoint of a red-starting path; `v` is an endpoint of a blue-ending path. They cannot be endpoints of the same path: alternating from red at `u` to blue at `v` uses an even number of edges, whereas every path from `L` to `R` has odd length. Swap red and blue on the path containing `v`. The resulting red matching belongs to `S+u+v`, and the blue matching belongs to `S`; all edges and therefore their total weight are preserved. This proves the inequality.

For two Bernoulli activations with common marginal `p`, replacing the independent pair by one shared Bernoulli (both present or both absent) changes expected `m_q` by `p(1-p)` times the displayed cross difference, hence cannot reduce it. Repeating conditionally over disjoint heavy pairs shows that paired independent heavy-state activation has at least as much expected recourse as **fully independent activation of every endpoint** with the same marginal probability. This is an exact reduction; it uses bipartiteness of the combined graph and nonnegative profits.

Consequently, the `alpha=3/4` independent-heavy theorem follows from the standalone inequality

`E m_q(R) >= (3/4) F_q(D)`, with all vertices activated independently with `p_v=(1+3D_v)/4`,

where `F_q(D)=max{q·y:y>=0, sum_{e incident v} y_e<=D_v}`. The next section proves this inequality. Equivalently, since `p_v=(1+3D_v)/4`, it says `E m_q(R)>=F_q(p-1/4)` for independent vertex activations with all `p_v in [1/4,1]`.

A tempting stronger inequality, `E m_q(R)>=F_q(p^2)`, is **false** despite the coordinatewise inequality `p_v^2>=(3/4)D_v`. Take a two-spoke unit-profit star whose center is always active (`p_c=1`) and whose leaves are independently active with `p_1=p_2=1/sqrt(2)`. The square capacities give `F_q(p^2)=min(1,1/2+1/2)=1`. But the expected matching value is only `1-(1-1/sqrt(2))^2<1`, since sometimes neither leaf is active. Thus square capacities cannot be used as a substitute for the boosted-linear target.

## Verified boundary cases

If all residual capacities equal `d`, then `F_q(D)=d·m_q(V)` by homogeneity and bipartite matching integrality. Fix an optimum matching `M`; keeping its edges whose endpoint pairs are active gives expected weight at least `p^2 m_q(V)`, where `p=(1+3d)/4`. Since `p^2-(3/4)d=(3d-1)^2/16>=0`, the desired inequality holds. A fluid edge joining the two endpoints of one heavy pair survives with probability `p>=p^2`, so the same argument covers it.

For any fixed `D,q`, an extreme optimum fluid vector `y` has a forest positive support: otherwise an even cycle supplies a nonzero signed perturbation preserving all vertex loads, contradicting extremality. Thus it is enough to test or prove the standalone inequality on weighted forests (the full graph's recourse dominates that on the chosen support). This reduction does not remove heavy-pair correlations; the supermodularity reduction above handles them separately.

The constant `3/4` is sharp for this independent-state scheme even on one fluid edge between two distinct heavy pairs. Put residual capacity `D=1/3` at its endpoints. Each is active with probability `1/2`, so the edge has expected recourse `1/4=(3/4)D`.

## Forest induction and full independent-activation theorem

Put `alpha=3/4` and `p_v=1/4+alpha D_v`, with `0<=D_v<=1`. First consider a weighted forest and any feasible target `y>=0` with `sum_{e incident v}y_e<=D_v`. We prove by induction on forest edges that

`E m_q(G[R]) >= alpha sum_e q_e y_e`.

Choose a leaf `v` and its neighbor `u`, write `e=uv`, `s=y_e`, and delete `v,e`. Replace `D_u` by `D'_u=D_u-s`, leaving all other target capacities unchanged. The restricted target is feasible, because its load at `u` fell by exactly `s`; also `D'_u>=0`. In the reduced random graph, `u` is active with probability `p'_u=p_u-alpha s`.

Condition on every activation except those of `u,v`. Let `A` be the reduced graph's matching optimum with `u` absent, and let `B>=0` be its additional optimum value when `u` is present. If `v` is present too, its sole edge allows the alternative value `A+q_e`; hence the full conditional expectation is

`A+p_u B+p_u p_v(q_e-B)_+`.

The reduced conditional expectation is `A+(p_u-alpha s)B`. Their difference is `alpha s B+p_u p_v(q_e-B)_+`, at least `alpha s q_e`: indeed `D_u,D_v>=s` gives

`p_u p_v >= (1/4+alpha s)^2 >= alpha s`, with difference exactly `(alpha s-1/4)^2`; split into the cases `B<=q_e` and `B>=q_e`. Averaging over the other activations and applying induction proves the claim. If a leaf edge has `s=0`, the same comparison remains valid and simply discards a nonnegative contribution.

For an arbitrary bipartite fluid graph and nonnegative profits `q`, choose an extreme optimum `y` of `F_q(D)`. The positive support of `y` is a forest: an even cycle, including a parallel-edge 2-cycle, admits a nonzero alternating signed perturbation preserving every vertex load, contrary to extremality. Applying the forest result on this support and observing that recourse in the full graph is at least recourse on the support yields

`E m_q(G[R]) >= alpha q·y = alpha F_q(D)`.

All statements above permit heterogeneous capacities, edge profits, and multiedges. They rely on binary vertex capacities only at the recourse stage, where bipartite fractional matching is integral.

## Transfer back to categorical heavy edges and divisible fluid

Suppose heavy physical edges have weight greater than `1/2`, their simple support is a matching, and the combined heavy-plus-fluid graph is bipartite. Parallel heavy types at a matched pair are allowed. Let `x_h` be each heavy edge's local-bin presence marginal, so `sum_{h in pair}x_h<=1`; let `y_e` be each fluid edge's target load, with `sum_{e incident v}y_e<=D_v:=1-sum_{h incident v}w_h x_h`. For a fixed global color, independently choose a categorical heavy state at each pair with `P(h)=alpha x_h`. The resulting residual scalar is the same at both pair endpoints and has mean `p_v=1-alpha(1-D_v)`.

For every nonnegative fluid profit vector `q`, the recourse optimum `F_q(R)` is concave in each heavy pair's common residual scalar. The chord inequality therefore replaces each independent real-valued pair state by an independent Bernoulli residual in `{0,1}` with the same mean without increasing expected recourse. In a bipartite combined graph, pair endpoints are on opposite sides, so opposite-side supermodularity above shows that splitting each Bernoulli pair into two independent endpoint activations also cannot increase expected recourse. The theorem just proved gives

`E F_q(R) >= alpha F_q(D) >= alpha q·y`.

Let `K` be the set of all average fluid-load vectors obtained by choosing, after each heavy-state outcome, any feasible fluid vector under its residual capacities. This is a compact convex downward-closed set. Its support function in every nonnegative direction `q` is `E F_q(R)`. The displayed inequalities imply `alpha y in K`: if separation used a direction with negative coordinates, replacing them by zero only raises the target scalar product and leaves the downward-closed support value unchanged. Hence conditional feasible fluid choices achieve exact coordinatewise expected load `alpha y`, alongside exact heavy marginals `alpha x_h`. This proves a `3/4` local-hull inclusion for the stated **divisible, no-supply-cap fluid model**. It does not make physical tiny edges indivisible or supply-limited, and by itself gives no uniform integer coloring theorem for them.

## Weighted star boundary case

The live boosted-linear inequality holds when the tiny support is one weighted star, with arbitrary heterogeneous residual capacities. Let `c` be its center, `D_c=d`, and sort leaf-edge profits decreasingly. For a prefix `J`, write `S=sum_{j in J}D_j`. The fractional optimum on that prefix is `min(d,S)`. The random matching optimum on the prefix is one if the center and at least one prefix leaf are active, and zero otherwise. Layer-cake expansion of profits reduces the weighted claim to

`p(d) P(any prefix leaf active | center active) >= (3/4) min(d,S)`, where `p(t)=(1+3t)/4`.

If the prefix includes the center's own heavy-pair partner, that leaf is certainly active conditional on the center's activation; the left side is `p(d)>=(3/4)d`, so the claim follows. Otherwise the prefix leaves lie in distinct heavy pairs in a bipartite combined graph, so their activations are independent. For fixed `S`, the ratio `min(d,S)/p(d)` is maximized at `d=min(S,1)`. Thus for `S<=1` it suffices to prove `P(any active)>=3S/(1+3S)`; for `S>=1`, truncate leaf capacities to a subvector of sum one and use monotonicity.

For one leaf, the last inequality reduces to `(3S-1)^2>=0`. For at least two leaves, independence and AM–GM give

`P(none active)=(3/4)^k product_j(1-D_j) <= (9/16) exp(-S) <= 1/(1+3S)`.

The last inequality follows because `(9/16)(1+3S)exp(-S)` is maximized at `S=2/3`, where it equals `(27/16)exp(-2/3)<1`. This proves every profit-prefix inequality and hence the weighted star claim. It does not settle arbitrary tiny forests, where matching choices couple several stars.
