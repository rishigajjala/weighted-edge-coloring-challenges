# Audit: capped 3/4 transfer for common-weight bipartite heavy components

3 October 2026. This is a scoped analytic theorem, not a physical finite-palette or unrestricted weighted-coloring result.

Let the combined support be bipartite. The heavy edges form an arbitrary bipartite multigraph; a one-color heavy set is a matching. All positive heavy types in each connected heavy-support component have one common weight `w` (different components may have different weights). Let `x` be a fractional bipartite matching vector, `D_v=1−Σ_{h∋v}w_hx_h`, and let a divisible fluid target `y` have vertex load at most `D_v`. Give fluid edge `e` a finite one-color cap `C_e≥12y_e`. Then a one-color law has heavy edge marginals `3x_h/4` and exact fluid means `3y_e/4`. The conclusion is a one-color hull inclusion for capped fluid. It does not assign finite physical tiny identities to one palette.

## Capped bipartite flow cross signs

For fixed edge profits `q≥0` and caps `C`, write `F_q(A,C)` for the optimal flow when vertices in `A` have unit capacity and other vertices capacity zero. For vertices `u,v` on opposite shores,

`F(S+u+v)+F(S)−F(S+u)−F(S+v)≥0`.

The previously audited alternating-flow exchange proves this even with edge caps: take optimal flows for `S+u` and `S+v`, subtract their edgewise minimum, orient the excess of the first flow left-to-right and of the second right-to-left, and swap all directed alternating trails from the right-side newly active vertex. Every edge's new flow lies between the two old values, so its cap is respected, and the sum of profits is unchanged.

For vertices `u,v` on the **same** shore, the reverse inequality holds. Take optimal flows `f` for `S+u+v` and `g` for `S`. Subtract their edgewise minimum and orient excess `f−g` left-to-right, excess `g−f` right-to-left. Both newly active left vertices are pure sources; neither has incoming excess. Decompose the directed excess into source-to-sink paths and cycles, and swap red/blue flow on every path originating at `v`. The flow `f'` then has no load at `v`, while `g'` gains its load there; `u` is untouched because no path can enter it. At intermediate vertices both color loads are unchanged. At a path sink the two changed loads move toward each other, so remain within their former feasible bounds; edgewise both changed flows lie between `f_e` and `g_e`, respecting `C_e`. Thus `f'` is feasible for `S+u`, `g'` for `S+v`, and their total profit equals that of `f,g`. The right-shore case reverses orientations. This gives same-shore submodularity.

Let `Φ_q(p)=E_{A∼independent Bernoulli(p)}F_q(A,C)` be the multilinear extension. Its mixed derivative in coordinates `u,v` is the expectation of the corresponding four-state cross difference. Hence this derivative is nonnegative for opposite shores and nonpositive for the same shore.

## Dependent rounding of heavy edges

Start from `z=3x/4` in the bipartite matching polytope and set `p_v(z)=1−Σ_{h∋v}w_h z_h`. Initially `p_v=1/4+3D_v/4`. While fractional heavy edges remain, choose an even cycle in their support, or, if the fractional support is a forest, a leaf-to-leaf path. Perturb successive edge values by alternating `+t,−t` until an edge hits zero or one, choosing the two boundary perturbations with barycentric probabilities that preserve each edge expectation. Fractional-support leaves have degree below one, so both perturbation directions are feasible; internal path degrees and all cycle degrees stay fixed. Eventually the heavy vector is an integral matching `M` with exact marginals `E1_M=z`.

An even cycle changes no vertex degree, hence leaves `Φ_q(p(z))` fixed. A path changes degree only at its endpoints. On an odd-length path those endpoints lie on opposite shores and their degrees change in the same direction; common weight in the heavy component gives equal-magnitude, same-sign changes in their `p` coordinates. The nonnegative cross derivative makes `Φ_q` convex along this segment. On an even-length path the endpoints are on the same shore and their degrees change in opposite directions; the nonpositive cross derivative again makes `Φ_q` convex. Because a multilinear extension has no diagonal second derivatives, these cross-signs are the entire second derivative. Jensen's inequality at each randomized perturbation gives `E_M Φ_q(p(M))≥Φ_q(p(z))`. The rounding decisions are independent of `q`, so one matching law works for every profit vector.

For an integral heavy matching `M`, the actual residual vector is `R_v(M)=p_v(M)∈[0,1]`. Joint concavity of capped flow in vertex capacities gives `F_q(R(M),C)≥Φ_q(p(M))` by comparing `R(M)` with independent binary vertex capacities of the same means. The capped independent-activation theorem (`five_hour_capped_activation_audit.md`) gives `Φ_q(p(z))≥(3/4)q·y` under `C≥12y`. Therefore `E_M F_q(R(M),C)≥(3/4)q·y` for every `q≥0`. The achievable mean capped-flow set conditional on this q-independent heavy law is compact, convex, and downward closed; support-function separation supplies one conditional policy with exact fluid means `3y/4`.

The common-weight hypothesis matters precisely at a path endpoint: with different incident heavy weights, the two activation-coordinate changes need not have equal magnitude, and the cross-sign alone no longer controls curvature along the rounding line.
