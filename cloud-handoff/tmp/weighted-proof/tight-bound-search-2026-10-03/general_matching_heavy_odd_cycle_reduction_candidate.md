# Interim odd-pseudoforest reduction for general matching-heavy divisible fluid

**Status (2026-10-03, inside the required five-hour audit window):** scoped `2/3` local-hull proof candidate for categorical heavy pairs whose simple support is a matching plus uncapped divisible fluid on arbitrary combined support. The cyclic-coupling step has been independently checked at the level of its binary-state transport, but the whole transfer remains under the requested extended audit. No unrestricted physical-edge-coloring claim follows.

## Live support at a local extreme point

The categorical elimination and linear-independence argument of `bipartite_matching_heavy_arbitrary_fluid_five_fourths_candidate.md` does not require bipartiteness until the last step. At a local-polytope vertex, each heavy pair has at most one effective categorical degree of freedom, represented by a nonzero multiple of the unsigned incidence column of its simple edge. Positive fluid edges have their usual unsigned incidence columns. All live columns are linearly independent.

For an arbitrary graph, a connected collection of unsigned edge-incidence columns is independent precisely when its support is a tree or a graph with exactly one cycle and that cycle is odd. An even cycle has the alternating kernel; any connected graph with at least two cycles has more edges than vertices and hence a kernel. Therefore each live connected component is a tree or an **odd unicyclic** graph. Heavy pairs are a matching, but fluid edges need not be.

Contract components of positive fluid edges. Live heavy-pair links form a pseudoforest. An odd cycle may contract to a loop (`k=1`, one live heavy pair with both ends in one fluid component), two parallel links between two components (`k=2`), or a longer cycle. The loop is the heavy-plus-two-fluid-spoke triangle mechanism. A fluid-only odd cycle has no live heavy variable within its component, by column independence, and can be handled deterministically.

## Two-coordinate Jensen estimate for one internal live heavy pair

Fix one positive-fluid component `C`, with deterministic full-state heavy pairs fixed as baseline loads. Suppose its private categorical guard variables also include at most one pair whose two endpoints lie inside `C`. Consider any vertex of this component's exact local polytope, temporarily restricting fluid recourse to the vertex's positive-fluid support. In each positive-fluid subcomponent, the same dimension count `m+Σ(s_p-rho_p)≤n` allows at most one random categorical pair. If its two endpoints lie in this subcomponent, its two possible states change residual capacities at both endpoints by the same absolute amount `delta≤1`. Along the line joining those two capacity vectors, optimal fluid recourse is monotone and has Lipschitz constant at most `L_u+L_v`, where `L_z` is the maximum incident fluid profit at `z`. Since each `L_z≤F_{C,q}(1)`, the two-state Jensen loss is at most

`p(1-p)delta(L_u+L_v)≤F_{C,q}(1)/2`.

If the random pair touches only one vertex of a positive-fluid subcomponent, its loss is at most that subcomponent's full-unit recourse divided by four. The same is true when its two endpoints lie in different positive-fluid subcomponents, after adding their one-coordinate losses. Summing disjoint subcomponents costs at most `F_{C,q}(1)/2`. Decomposing an arbitrary local point into component-local vertices yields a full-marginal heavy law satisfying

`E F_{C,q}(R)≥q·y_C-F_{C,q}(1)/2` for all `q≥0`.  (1)

The law can be selected independently of `q`; the recourse policy may depend on `q`.

## The `k=1` contracted-cycle shape

At a global local-polytope extreme point, suppose each live odd unicycle that contains a heavy link has exactly one heavy link within one positive-fluid component. Delete that link conceptually; all remaining live heavy links connect fluid components as a forest. Apply (1) to the core component with the internal link and the private-guard additive bound `F_C(1)/4` to every other component. The full-marginal component laws agree on each shared external live heavy pair's categorical marginal. Glue them along the contracted forest by conditioning on the shared pair state. Deterministic heavy pairs have fixed full states.

The resulting global full-marginal heavy law has

`E F_q(R_full)≥q·y-(1/2)Σ_C F_{C,q}(1)`.

Use one global coin: this full law with probability `2/3`, empty heavy state with probability `1/3`. The empty state contributes `Σ_C F_{C,q}(1)`, cancelling the half-loss and giving expected recourse at least `(2/3)q·y`. Support-function separation then gives exact scaled fluid means, as in the bipartite note. This proves the `k=1` shape if the component-local estimate and forest gluing survive independent audit. The heavy edge across two fluid-spoke leaves with unit weight and local presence `1/2` attains the half-loss, so this estimate cannot simply be improved in general.

## Cycles through two or more fluid components

Suppose a live odd cycle visits `k≥2` distinct positive-fluid components, linked by `k` live heavy pairs. At each component the two cycle links are distinct heavy pairs, and all its live heavy links are external. Thus the private-component full-law lemma supplies a component heavy-state law with additive recourse loss at most `F_C(1)/4`, preserving the exact categorical marginal on every link. These component laws may have incompatible correlations around the cycle.

Fix a nonnegative profit vector `q`. Choose on the cycle a component `C_*` minimizing its full-unit fluid recourse `F_{C,q}(1)`. Temporarily omit its factor. The other cycle components form a path, so glue their full laws conditionally on the shared categorical heavy states; this produces some joint law `nu` for the two cycle link states `A,B` incident to `C_*`. Each link's **individual** marginal still equals its original categorical marginal. Encode each of the two possible states on a live link as `0` (the lighter/no-heavy state) and `1` (the heavier state); the state has the same ordering at both endpoints because the selected heavy type has the same weight there.

Let `mu` be the original full law at `C_*` on `(A,B,Z)`, where `Z` records every other incident heavy-link state and any private component randomness. The `(A,B)` marginals under `mu` and `nu` agree separately. A binary pair law with fixed marginals is determined by `theta=P(A=1,B=1)`, and the two theta values differ by `delta` with `|delta|≤1/2`.

If `nu` has larger theta, take `delta` mass from cell `10` and `delta` from cell `01` under `mu`. Change only the bit `A`, sending `10→00` and `01→11`; retain the sampled `Z` in each piece. This raises theta by `delta`, preserves both one-link marginals and the **entire joint marginal of Z**. The first change removes a heavier guard state, so fluid recourse at `C_*` cannot decrease. The second adds a heavier guard state and costs at most `F_{C_*,q}(1)` per unit of moved mass. The reverse theta adjustment uses `11→01` (improves recourse) and `00→10` (costs at most `F_{C_*,q}(1)`). The needed source-cell masses exist because both theta values lie in the Fréchet interval for their common one-bit marginals. Hence one obtains a modified component law `mu'` with pair law `nu`, unchanged other-link marginals, and recourse loss at most

`delta F_{C_*,q}(1)≤F_{C_*,q}(1)/2≤(1/4)Σ_{C on cycle}F_{C,q}(1)`;

the final inequality uses `k≥2` and the minimum choice of `C_*`. Now glue `mu'` to the path law conditional on their common pair `(A,B)` state, then glue all branch trees. The modified law still has correct marginals on every branch link because `Z` was preserved samplewise. Thus the full heavy law pays at most the private-component quarter-loss plus this extra quarter-loss, giving

`E F_q(R_full)≥q·y-(1/2)Σ_C F_{C,q}(1)`

over this live unicyclic component and its attached branches. Distinct live components can be handled separately. Combined with the tree components and `k=1` loop cases, this inequality holds globally for each `q≥0`.

Mix the resulting full heavy law with the global empty-heavy state in proportions `2/3` and `1/3`. The empty state's fluid recourse `F_q(1)=Σ_C F_{C,q}(1)` cancels the half-loss, so the mixture has heavy type marginals `(2/3)x_h` and support value at least `(2/3)q·y`. A standard downward-closed support-function separation gives exact fluid means `(2/3)y`. Applying this to each extreme local point and mixing proves the stated `2/3` inclusion **within the categorical matching-heavy plus uncapped-fluid model**, subject to the ongoing full audit.

## Exact two-link cycle diagnostic

A five-cycle makes the cyclic consistency issue explicit. Use two disjoint **unit-weight** heavy links `A_1B_1` and `A_2B_2`, each of local presence `1/2`. The fluid support consists of one edge `A_1A_2` and a two-edge path `B_1--c--B_2`; put fluid target `1/2` on each of these three edges. Every vertex's local load is one, so the point is locally feasible. Give each fluid edge unit profit.

At scaled heavy marginals `alpha/2`, let `theta` be the probability both heavy links occur in one color. The one-edge fluid component has expected recourse `P(no heavy)=1-alpha+theta`. The two-edge path has one unit of recourse unless both of its leaves are heavy, so its expected recourse is `1-theta`. Total recourse is exactly `W(alpha)=2-alpha`, independent of the heavy-link coupling. The target profit is `3alpha/2`; thus this scoped point obstructs `alpha>4/5`, a `5/4` mixed-fluid gap. Its two fluid components prefer opposite correlations of the same pair of heavy-link states. The general `2/3` theorem candidate has slack here; the single-link triangle remains its sharp `3/2` obstruction.
