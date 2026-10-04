# Bipartite heavy-plus-divisible-fluid sharpness audit

**Status (2026-10-03):** scoped exact calculations, not a sharp constant for the full mixed model or an unrestricted weighted-edge-coloring result. All graphs below are bipartite, fluid is uncapped and divisible, and a one-color configuration selects a matching of categorical heavy edges and routes fluid subject to unit vertex capacities. The heavy weights in the lower example are strictly above `1/2` except at its limiting endpoint.

## An exact `5/4` lower limit from one fluid edge

Fix `0<y<1/2`. Use a four-vertex path with one fluid middle edge `uv` and two disjoint heavy guard edges at `u,v`. The `u` guard has weight `1-y` and local presence `x_u=1`; the `v` guard has weight `1` and local presence `x_v=1-y`. Set the fluid target on `uv` to `y`. The local capacity at each of `u,v` is exactly saturated:

`(1-y)x_u+y=1`, and `1*x_v+y=1`.

At a proposed scale `alpha`, the heavy guard marginals must be `alpha` and `alpha(1-y)`. In any joint law, let `A` be the event that the `u` guard is present and `B` that the `v` guard is present. Fluid recourse is zero on `B`, is `y` on `A\B`, and is `1` on the complement of `A∪B`. Consequently

`E F = P((A∪B)^c)+y P(A\B) = 1-2alpha+2alpha*y+(1-y)P(A∩B)`.

This is maximized by nesting `B⊆A`, because `P(B)=alpha(1-y)≤P(A)=alpha`. The maximum is

`W(alpha)=1-alpha+alpha*y^2`.

The required fluid marginal is `alpha*y`, so feasibility requires

`alpha ≤ 1/(1+y-y^2)`.

This requirement is also sufficient for this three-coordinate target: take the nested law, use up to `F` units of fluid on each state, and thin fluid to the required mean. The limiting obstruction as `y↑1/2` is `alpha≤4/5`, equivalently a mixed-model local-hull gap at least `5/4`. At `y=1/2` the `u` guard has weight exactly `1/2`, so the strict-heavy model gets the limit but not that exact endpoint.

This example does **not** establish a `4/3` lower bound for the divisible-fluid model. It also shows why sharpness of an independent-vertex activation inequality at `3/4` is not sharpness of the physical mixed hull: heavy-guard events can be coupled positively.

## The established bipartite `4/3` construction becomes globally feasible when its path bundles are fluid

Consider the graded-path construction in `tmp/weighted-proof/lower-bound-four-thirds.md`: path vertices `v_0,...,v_m`, guard edge at each vertex, strictly decreasing path weights `1/2>w_0>...>w_{m-1}>1/3`. For `i<m`, the guard at `v_i` has weight `1-w_i`; the terminal guard at `v_m` has weight `1`. Its normalized local data are guard presence `2/3` at every vertex and path-fluid amount `y_i=2w_i/3` on `v_iv_{i+1}`. These data arise by replacing each path bundle of `2N` physical edges by divisible fluid of total load `2Nw_i` and normalizing by `3N` local bins.

We give a globally feasible law for **the full unscaled local point**, `alpha=1`. Let `H` be one Bernoulli bit of probability `2/3`. If `H=1`, choose all disjoint guards; if `H=0`, choose no guards. Define the `H=1` fluid amounts backwards:

`f_{m-1}^{(1)}=0`, and `f_{i-1}^{(1)}=w_i-f_i^{(1)}` for `i=m-1,m-2,...,1`.

Induction using decreasing positive weights gives `0≤f_i^{(1)}≤w_i` for every `i`. At every internal vertex `v_i`, the two fluid amounts sum to `w_i`, exactly its capacity after its guard is selected. At `v_0`, its single fluid amount is at most `w_0`; at terminal `v_m` the amount is zero.

If `H=0`, set `f_i^{(0)}=2(w_i-f_i^{(1)})≥0`. At an internal vertex `v_i`, its total fluid is

`f_{i-1}^{(0)}+f_i^{(0)} = 2(w_{i-1}+w_i-f_{i-1}^{(1)}-f_i^{(1)}) = 2w_{i-1}<1`.

The endpoint loads are at most `2w_0<1` and `2w_{m-1}<1`. Finally the mean fluid on path edge `i` is

`(2/3)f_i^{(1)}+(1/3)f_i^{(0)}=2w_i/3=y_i`.

Thus every normalized guard and fluid coordinate is realized exactly. In particular the known `4/3` **physical** lower bound relies on indivisibility of its `(1/3,1/2)` path edges; the same local vector gives no gap at all once those bundles become uncapped divisible fluid. This does not rule out a different `4/3` mixed-fluid witness.

## Current boundary

The calculations establish `5/4` as a lower-limit factor for the heterogeneous-heavy-plus-uncapped-fluid bipartite class. The existing `3/4` transfer theorems give an upper factor `4/3` in their stated subcases, but no matching `4/3` mixed-fluid lower witness has been identified here. The best factor for arbitrary categorical heavy support and uncapped divisible fluid remains open in this scratch program.

## Targeted short-path diagnostics and a local-vertex reduction

The reproducible finite-grid probe `mixed_fluid_path2_gap_probe.py` checks a two-edge fluid path with one independent categorical heavy guard at each of its three vertices. For each weight triple in `{1/2,3/5,3/4,1}^3`, it enumerates vertices of the five-coordinate local capacity polytope and vertices of every one-color guard-state fluid polytope. A linear program computes the exact *formulation's* gauge numerically for each local vertex. Among the 64 tested triples the largest computed gap is `5/4`; each displayed maximizer has one fluid coordinate zero, reducing to the preceding one-edge obstruction. This is a finite numerical diagnostic, not a proof for arbitrary real weights, parallel heavy types, or heavy links between guard vertices.

There is a simple exact sparsity fact in the independent-guard template. Suppose the positive fluid support is a tree on `n` vertices, with exactly one private heavy guard probability `x_v` at each vertex. A local-polytope vertex with all `n-1` tree fluid coordinates positive has at most one fractional `x_v`. Indeed there are `2n-1` variables. At most `n` independent capacity inequalities can be active, while no fluid nonnegativity inequality is active. At least `n-1` guard box inequalities must therefore be active, fixing at least `n-1` guard probabilities to `0` or `1`. The same argument on a forest leaves at most one fractional guard per connected component. This observation does not extend directly to arbitrary shared heavy edges, where a heavy variable enters two vertex rows.

## A forced full-law gap of `1/3` that scales better than `5/4`

There is a different four-heavy-edge path `v_R--a_L--b_R--u_L--c_R`, with edges `e_1,...,e_4` in path order and heavy marginals `(2/3,1/3,2/3,1/3)`. Give `e_1,e_2,e_4` weight `1` and `e_3` weight `1/2` as a limiting case; for strict heaviness take `e_3=1/2+epsilon` and adjust the fluid target continuously. Add fluid edge `uv` of target `y=1/3` in the limiting case. Both fluid endpoint load inequalities are tight. The three internal path vertices have categorical heavy degree exactly one, so the **full** heavy law is forced to select `{e_1,e_3}` with probability `2/3` and `{e_2,e_4}` with probability `1/3`. Both states leave zero recourse on `uv`, showing that the unscaled additive recourse gap can approach `1/3`, even for one fluid edge. Consequently a general `4/5` transfer cannot follow solely by mixing a full matching law with the empty matching.

At scale `alpha∈[3/4,1]`, however, the exact optimized recourse is `W(alpha)=3(1-alpha)/2`. For any heavy matching indicator vector `s`, direct inspection of the eight path matchings gives

`F_{uv}(s) ≤ 3/2-(s_1+s_2)/2-s_3-s_4`.

Its expectation under the prescribed scaled marginals is `3(1-alpha)/2`. Equality is attained by the following five matchings, listed with their probabilities:

`{e_3}:1-alpha`, `{e_2}:1-alpha`, `{e_2,e_4}:(4alpha-3)/3`, `{e_1,e_4}:1-alpha`, and `{e_1,e_3}:5alpha/3-1`.

The probabilities are nonnegative and sum to one throughout the stated interval. The required fluid marginal `alpha/3` fits exactly when `alpha≤9/11`; the obstruction's factor is therefore `11/9`, below the simpler four-vertex `5/4` lower limit. The computation exposes the relevant mechanism: scaling creates new matching states that repair a forced bad full-law correlation.
