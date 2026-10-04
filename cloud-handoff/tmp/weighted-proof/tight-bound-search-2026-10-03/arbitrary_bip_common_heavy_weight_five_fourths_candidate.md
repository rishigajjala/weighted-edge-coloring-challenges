# Candidate 4/5 mixed-hull transfer for arbitrary bipartite heavy support at one common weight

**Interim status (2026-10-03, within the user's required five-hour exploration period):** a complete candidate argument under a precise common-weight assumption, independently cross-checked in discussion but still subject to further audit. It is not an unrestricted weighted-edge-coloring bound. Fluid edges are **uncapped and divisible**; it says nothing about exact physical small-edge stocks or integer colors. Arbitrary parallel heavy types are allowed provided they all have the same weight `w∈[1/2,1]`. The combined support graph is bipartite.

## Claim and support formulation

Let `x_h>=0` be categorical heavy marginals and `y_e>=0` divisible fluid loads with

`H_v:=Σ_{h∋v}x_h<=1`, `w H_v+Σ_{e∋v}y_e<=1` at every vertex.

The candidate claim is that `((4/5)x,(4/5)y)` lies in the convex hull of one-color mixed states: selected heavy edges form a matching, and fluid flow respects the residual vertex capacity `1−w` at a heavy-covered vertex and `1` elsewhere. For any fixed `x`, the allowable fluid-mean vectors form a convex downward-closed set. It suffices to show, for each nonnegative fluid profit `q`, a heavy matching law with marginals `(4/5)x` and expected maximum fluid profit at least `(4/5)q·y`. The heavy law may depend on `q`.

By convexity of the local polytope and of the target hull, it suffices to prove the claim for a local-polytope extreme point `(x,y)`. Fix one such point and `q`.

## Completion and the incidence forest

At every original vertex `v`, add a private dummy fluid leaf `d_v` with a zero-profit edge of amount

`s_v=1−w H_v−Σ_{e∋v}y_e>=0`.

The augmented point satisfies equality `w H_v+Σ_{e∋v}y_e+s_v=1` at every original vertex. This is an affine isomorphism of the original local polytope: each `s_v` is uniquely determined; its private-leaf bound `s_v<=1` is redundant. Thus extremality is preserved. Private dummy edges are only a proof device and need not be selected in the final mixed state.

Scale each heavy variable to `z_h=w x_h`. At an original vertex with `H_v<1`, its sole active structural row is the total equality; call its row node `J_v`. Heavy and fluid columns alike have coefficient one there. At a vertex with `H_v=1`, keep the active categorical equality `Σ z_h=w` as row node `A_v`, and subtract it from the total equality to obtain the fluid-only equality `Σ_{e∋v}y_e+s_v=1−w` as row node `B_v`. A heavy column touches `A_v`; a fluid column touches `B_v`. At either endpoint, the row node inherits its original bipartition shore. A dummy leaf row is active only if `s_v=1`; otherwise its column is one-ended at the original row node.

Consequently the active equality matrix on positive variables is the unsigned incidence matrix of a bipartite graph with possible one-ended dummy columns. Every cycle of positive, non-bound columns gives a nonzero alternating-sign perturbation preserving all active rows. All inactive inequalities have slack and all such variables are interior to their nonnegativity/individual bounds, so a sufficiently small perturbation in both signs contradicts extremality. A positive heavy variable at individual upper bound `x_h=1` is isolated between categorical row nodes because it saturates both endpoint heavy degrees; it cannot participate in a cycle. A positive fluid/dummy variable at its maximum unit amount likewise has no other positive incidence at its endpoints. Hence the entire positive-column incidence graph has no cycle.

Let `C` range over connected components of the positive fluid-edge support **including dummy edges**. Contract each such fluid component in the active incidence forest, while retaining every categorical-only row node `A_v` separately. Keep positive heavy columns as links. The resulting heavy-link factor graph is a forest. A positive heavy link never has both endpoints in the same fluid factor: that would close an incidence cycle. The completion is essential here: every heavy endpoint has an active row, so a heavy link cannot disappear as a one-ended stub at an original vertex.

## A local law at one fluid factor

Fix a positive-fluid component `C`. At its original vertices of `J` type, aggregate all incident positive heavy-link marginals into one coverage coordinate `p_v=Σ_{h∋v}x_h` in `[0,1]`. Their selected heavy identities will be restored after choosing coverage. At its original vertices of `B` type, the heavy degree is one in every full-marginal law, so fluid residual capacity is deterministically `1−w`; no random guard variable is needed inside `C`. Dummy leaves have capacity one. Temporarily replace every external heavy link at a `J` vertex by a private categorical guard; locally only its aggregate coverage `p_v` matters because all heavy weights equal `w`.

Consider the component-local polytope of these `p_v` coordinates and fluid amounts on the edges of `C`, with `0<=p_v<=1`, `y_e>=0`, and vertex capacities `Σ_{e∋v}y_e+w p_v<=1` at `J` vertices, `Σ_{e∋v}y_e<=1−w` at `B` vertices, and `Σ_{e∋v}y_e<=1` at dummy leaves. Fix `p_v=0` if no positive heavy link leaves `v`. The original restriction `(p,y_C)` belongs to this polytope. Decompose it into its vertices.

At any such local vertex, its positive fluid support is a forest (a cycle gives an alternating perturbation). In one nontrivial positive-fluid component `S` with `n_S` vertices and `n_S−1` positive fluid columns, at most one coverage coordinate can be strictly between zero and one: two such `p` columns plus the fluid columns outnumber the at-most-`n_S` active vertex-capacity rows, yielding a two-sided perturbation. An isolated vertex cannot host a fractional `p`, since `w p<1` for `p<1` and it has no positive fluid column, so its capacity row is slack. Thus each positive-fluid subcomponent has at most one genuinely random coverage bit; all other local capacities are deterministic.

Let `F_{q,S}(r)` be maximum fluid profit on the positive edges of `S` under residual capacities `r`, and `K_S=F_{q,S}(1)` (unit capacities on all its vertices). For a subcomponent with one fractional coverage `p`, round that bit to `0` or `1` with mean `p`; the resulting capacities differ at only one vertex by at most `w`. Since increasing one vertex capacity by `a` can improve fluid optimum by at most `a K_S` (delete at most `a` incident flow from an optimum, each unit worth at most the highest incident profit, which is at most `K_S`), the two-point concave-Jensen gap is at most `p(1−p)wK_S<=K_S/4`. If no fractional bit, there is no loss. Restricting recourse to each positive subcomponent, summing, and using the local vertex's feasible fluid vector gives expected recourse at least `q·y^{vertex}−(1/4)Σ_S K_S`. The subcomponents have disjoint vertices, so their unit-capacity optimal flows combine in `C`, whence `Σ_S K_S<=K_C:=F_{q,C}(1)`. Averaging the local vertex decomposition yields a full-marginal component law with expected fluid recourse at least

`q·y_C−K_C/4`.  (1)

For each `J` vertex with original `p_v>0`, whenever its coverage bit is one choose exactly one outgoing heavy identity `h` with conditional probability `x_h/p_v`. This is a well-defined categorical choice; it preserves every incident link's marginal `x_h`. It does not change the component fluid recourse because the weight is common. If `p_v=0`, no outgoing link is selected. Different vertices in `C` may select their own links simultaneously.

## Forest gluing and the one global empty state

At each categorical-only row node `A_v`, take a one-hot law on incident positive heavy links with probabilities `x_h`, summing to one because `H_v=1`. Each heavy link has the same binary selection marginal `x_h` at its two endpoint factors. Since the factor graph is a forest, glue all factor laws along links by conditioning successive factors on their shared link's selected/unselected state. This preserves every factor's joint law and makes each heavy link selected consistently at both ends. The resulting selected heavy edges form a matching: a `J` vertex has at most one local chosen identity, while an `A` vertex has exactly one. Every `B` vertex's heavy occupancy is deterministically one and therefore its fluid residual `1−w` is respected. The component fluid laws are feasible simultaneously because positive fluid components have disjoint vertices except for split `A/B` copies, and only the `B` copy carries fluid there.

Summing (1), the resulting **full-heavy-marginal** law has expected fluid recourse at least

`q·y−(1/4)Σ_C K_C`.

The empty heavy matching offers fluid recourse `K=F_q(1)`. All target-positive original fluid edges lie in the disjoint components `C`; dummy edges have profit zero. Their unit-capacity optimal flows combine, so `K=Σ_C K_C` when recourse is restricted to target-positive fluid edges. Use the full-heavy law with probability `4/5` and the empty-heavy law with probability `1/5`. Heavy marginals become `(4/5)x`, while expected fluid recourse is at least

`(4/5)(q·y−K/4)+(1/5)K=(4/5)q·y`.

Nonnegative-profit support-function separation gives a feasible joint mixed-state law with exact fluid means `(4/5)y`, proving the claimed scoped inclusion if every step above survives final audit.

## What remains outside the claim

The common weight is essential to the local aggregate-coverage reduction. If heavy types at a vertex have different weights, their identities change that vertex's residual by different amounts, and a positive-fluid factor can have several independent random weighted states even when its aggregate heavy occupancy is fixed. The proof also relies on uncapped divisible fluid for the one-coordinate sensitivity bound and for component recourse. It does not prove the original physical multigraph 4/3 bound, where each small physical edge is indivisible and has finite stock, nor does it yield a uniform integer palette.

## Audited relaxation of the equal-weight hypothesis

The incidence-forest and local-factor arguments actually require less than one global `w`. At the fixed mixed-local extreme under consideration, assume only that **at every vertex with tight categorical heavy degree `H_v=1`, all positive incident heavy types have the same weight `w_v`**. The weights may differ between such vertices and may be arbitrary at vertices with `H_v<1`. Under this pointwise condition, the same `4/5` transfer argument applies to that extreme.

Indeed, at a tight-heavy vertex scale its categorical row by its common incident weight `w_v`, and subtract it from the total equality. The resulting rows are again a heavy-only row with right side `w_v` and a fluid-only row with right side `1−w_v`. At a slack-heavy vertex, use the unsplit total row, scaling each individual heavy column by its own weight `z_h=w_h x_h`. Every positive column again has unit coefficients at its active endpoint rows, so the completed incidence graph and its contracted factor graph are forests. A tight-heavy vertex has deterministic residual `1−w_v` in every full-marginal heavy law.

At a slack-heavy fluid-factor vertex, retain **one categorical coordinate per outgoing heavy type** instead of aggregating coverage. The component-local polytope has inequalities `Σ_h t_h<=1` and `Σ_h w_h t_h+Σ_e y_e<=1` there. In a local vertex, let `s_v` be the number of positive categorical types at `v` and `ρ_v=1` if the categorical row is tight, zero otherwise. Its non-bound categorical degrees of freedom number at least `s_v−ρ_v`. If a positive-fluid subcomponent has `n` vertices and `n−1` positive fluid columns, two such categorical degrees of freedom would give more free columns than active vertex-load rows, contradicting extremality. Thus across that subcomponent there is at most one nontrivial categorical group. It has either one positive type plus absence, or two positive types summing to one; in either case its capacity is a two-point random variable in `[0,1]`. A one-coordinate `K_S`-Lipschitz recourse bound gives Jensen loss at most `K_S/4`. Isolated vertices cannot have a nontrivial categorical group at an extreme, because with no positive fluid their weighted-load row is slack or duplicates the categorical equality. Summing over disjoint subcomponents again costs at most `K_C/4`. Sampling directly from each local categorical group preserves every outgoing heavy identity marginal, so the same tree gluing and one global empty-heavy coin complete the transfer.

A clean input-wide corollary is obtained when **each connected component of the positive heavy support has a common weight** (equivalently, every vertex's incident positive heavy types have a common weight). Then every local extreme satisfies the pointwise condition, so the scoped `4/5` mixed-hull inclusion holds for the whole local polytope. The still-open obstruction is heterogeneous positive heavy weights meeting at a vertex whose categorical degree is tight at an extreme: its heavy-degree and weighted-load rows cannot be split into unit-incidence rows by one column scaling. This paragraph is an interim candidate extension, still under the five-hour audit requirement.
