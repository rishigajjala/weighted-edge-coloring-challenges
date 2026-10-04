# Shared-profile heavy components: capped bipartite 3/4 transfer

4 October 2026. Scoped one-color research result; it does not itself give a finite physical palette or an unrestricted weighted edge-coloring bound.

## Statement

Let the combined heavy/tiny support be bipartite. In each connected component `P` of the heavy simple support, suppose every endpoint-pair bundle `a=uv` has the same **conditional heavy weight profile** `lambda_P`: its fractional type marginals are

`x_{a,b}=x_a lambda_{P,b}`, with `sum_b lambda_{P,b}=1` and type weight `w_{P,b}`.

Different components may have different profiles. Assume `sum_{a at v}x_a<=1`. Put `D_v=1−sum_{a,b at v}w_{P,b}x_{a,b}`, and let tiny target `y` have incident sum at most `D_v`. Every tiny edge has cap `C_e>=12y_e`. Then there is a law on categorical heavy matchings, independent of the tiny profit vector, and conditional feasible capped tiny flows, whose heavy means are `3x_{a,b}/4` and tiny means are `3y_e/4`.

The hypothesis is stronger than a common mean weight: the entire conditional weight distribution must agree across all endpoint-pair bundles of a heavy component. Parallel physical identities may be aggregated into type classes. The result concerns the one-color divisible hull; physical identities still require a separate palette argument.

## Real-capacity signed cross inequalities

For a fixed nonnegative tiny-profit vector `q`, edge caps `C`, and real vertex capacities `r in [0,1]^V`, let `F_q(r,C)` be the capped bipartite flow optimum. Fix all coordinates other than `u,v`, and write `r_u^0<=r_u^1`, `r_v^0<=r_v^1`. The signed cross differences are

* `F(1,1)+F(0,0)<=F(1,0)+F(0,1)` if `u,v` lie on the same shore;
* `F(1,1)+F(0,0)>=F(1,0)+F(0,1)` if `u,v` lie on opposite shores.

The `0,1` notation refers to the two chosen real capacities, not necessarily zero and one. Edge caps are arbitrary and fixed.

For the first inequality, choose optimal red flow `f` for `(1,1)` and blue flow `g` for `(0,0)`. Remove their common edgewise minimum and orient red excess left-to-right and blue excess right-to-left; take `u,v` on the left. If `f_v>r_v^0`, then `f_v−g_v>=f_v−r_v^0`. In a directed path/cycle decomposition, `v` is a net red source of `f_v−g_v`, so transfer precisely `delta=(f_v−r_v^0)_+` units along paths starting at `v`, swapping red and blue excess on those paths. The resulting red flow has `v`-load at most `r_v^0`, while the blue flow has `v`-load at most `r_v^1` because its new load lies between `g_v` and `f_v`. At any other path endpoint, both changed loads lie between the old red and blue loads. If a transferred path ends at `u`, it is a blue-excess sink, so `g_u>f_u` and the new blue load decreases; hence blue remains within its lower `u` cap. A path through `u` leaves both loads there unchanged. All remaining vertices have unchanged or between-old endpoint loads. Every new edge amount lies between `f_e` and `g_e`, respecting `C_e`; the sum of the two flow objectives is unchanged. Thus the resulting flows are feasible for `(1,0)` and `(0,1)` and prove the inequality. If `f_v<=r_v^0`, no transfer is needed. The right-shore case reverses orientations.

For opposite shores, take red optimal for `(1,0)` and blue optimal for `(0,1)`. At the right-side vertex `v`, if `g_v>r_v^0`, it is a net blue source in the same oriented difference flow. Transfer `delta=(g_v−r_v^0)_+` units of blue excess along paths beginning there, making blue feasible for `(0,0)` and red feasible for `(1,1)`. If a path ends at the left-side `u`, the new blue load moves toward the old red load; since blue's old `u` load obeyed its lower cap, its new load cannot increase past that old cap in the relevant sink orientation. Equivalently, inspect the red/blue excess at `u`: a path ending at `u` is blue excess there, and the swap decreases blue load. The same edge-cap and intermediate-vertex reasoning proves the opposite-shore inequality.

This partial-swap proof is the needed extension of the previously audited binary-activation signs to arbitrary **real** capacity increments. It should be checked against a formal alternating-trail decomposition before being promoted to a publication proof.

## Multilinear cover function and pipage rounding

Within each heavy component `P`, independently sample a weight `W_v` with profile `lambda_P` at each *covered vertex* `v`, and give it residual capacity `1−W_v`; uncovered vertices have capacity one. For a set `S` of covered vertices let

`f_q(S)=E_{(W_v)_{v in S}} F_q(r(S,W),C)`.

Since both covered-vertex capacity changes are negative, the real-capacity inequalities retain their signs after averaging the independent weights: `f_q` is submodular for two vertices on the same shore and supermodular for opposite shores. Let `Psi_q(t)=E_{S~independent Bernoulli(t_v)}f_q(S)`. This is multilinear and has the same mixed-derivative signs.

Aggregate each heavy endpoint-pair bundle to one edge with `x_a=sum_b x_{a,b}`. Put `z=3x/4` in the bipartite matching polytope and `t_v(z)=sum_{a at v}z_a`. Standard alternating-cycle/path dependent rounding of `z` has the following effect: a cycle leaves all `t_v` fixed; a path changes only its endpoint `t` coordinates, with the same sign at opposite-shore endpoints (odd path) and opposite signs at same-shore endpoints (even path). The corresponding signed mixed derivative makes `Psi_q(t(z(s)))` convex in the path perturbation `s`. Barycentric random choice of the two feasible perturbation endpoints therefore does not reduce its expectation. Continue until `z` is an integral matching `M`; the matching law is determined solely by `z`, so it is independent of `q`, and

`E_M Psi_q(1_{covered(M)}) >= Psi_q(t(z))`.

The use of a common profile is exactly what permits `Psi_q` to depend on `z` through aggregate cover probabilities `t_v` alone. If bundles have different profiles, an internal path vertex can keep the same cover probability while changing its weight law, so this two-endpoint convexity argument no longer applies.

## Restore physical categorical weights

For an integral matching `M`, `Psi_q(1_{covered(M)})` gives independent endpoint weights drawn from `lambda_P`. Correlate the two endpoint weights on each selected matching edge by replacing their independent pair `(W_u,W_v)` with a shared `W~lambda_P`. Equivalently, the two endpoint residual capacities become comonotone. The opposite-shore real-capacity supermodularity implies this operation cannot decrease expected `F_q`: the comonotone coupling maximizes expectation of a supermodular function among couplings with fixed one-dimensional marginals. Apply this one selected edge at a time, conditioning on all other weights. Draws on different selected edges remain independent. The selected edge's type is now a single categorical draw `b~lambda_P`, so its marginal is `(3/4)x_a lambda_{P,b}=(3/4)x_{a,b}`.

At the initial fractional vector, the independent residual capacities at vertices have means

`p_v=1−(3/4)sum_{a at v}x_a E_{lambda_P}W = 1/4+(3/4)D_v`.

Joint concavity of `F_q` in vertex capacities, first conditional on these independent residuals and then via Bernoulli splitting, gives

`Psi_q(t(z)) >= E_{A_v~independent Bernoulli(p_v)}F_q(1_A,C)`.

The capped independent-activation theorem gives the right-hand side at least `(3/4) q·y` when `C>=12y`. Thus the same q-independent categorical matching law satisfies `E F_q(R(M,W),C)>=(3/4)q·y` for **every** nonnegative `q`. Compact convex downward-closed support-function separation gives one conditional capped tiny-flow policy with all coordinate means exactly `3y/4`.

## Scope and physical bridge

This provides the abstract capped input of `bounded_heavy_component_transfer_interface.md` if every heavy component has bounded size `h`, so its state menu is bounded after heavy bucketing. Combined with the audited sparsify/localize/finite-label bridge, it suggests a scoped physical `(4/3+epsilon)N+O_{epsilon,h}(1)` result for bipartite combined support and bounded heavy components with a common type-weight profile per component. The bridge still needs a final integrated write-up and parameter audit. Unbounded heavy components have unbounded categorical state menus for the current exact-field block; arbitrary profiles and general graphs remain outside this argument.
