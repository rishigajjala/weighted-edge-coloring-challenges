# Interim 5/4 local-hull transfer for matching heavy support and arbitrary divisible fluid

**Status (2026-10-03, during the requested five-hour research period):** proof candidate, independently under audit. This is **only** the mixed model below; it does not color indivisible physical small edges or settle the unrestricted weighted-edge-coloring coefficient. It improves the earlier `3/4` fluid transfer candidate to `4/5` if all steps survive audit.

## Exact model and proposed conclusion

Let the combined support be a finite bipartite loopless multigraph with unit vertex capacities. Heavy physical types have weights in `(1/2,1]`, but only their one-color categorical state matters here: all heavy types between a fixed simple pair form one categorical group, at most one type from that pair may be present, and the **simple support of heavy pairs is a matching**. Different heavy pairs are vertex-disjoint. Fluid edges may have arbitrary bipartite support and parallel multiplicity; their one-color amounts are nonnegative real numbers with **no per-edge supply caps**. A one-color configuration selects a heavy categorical state independently of feasibility of the fluid amounts, then chooses fluid amounts satisfying the residual unit capacities at all vertices.

For heavy type `h` let `x_h` be its local presence, and for fluid edge `e` let `y_e` be its local mean amount. Since at most one heavy pair touches each vertex, the exact one-vertex local polytope is

`P_loc={ (x,y)≥0: Σ_{h in pair p}x_h≤1 for every heavy pair p; Σ_{h∋v}w_h x_h+Σ_{e∋v}y_e≤1 for every vertex v }`.

The candidate conclusion is `(4/5)P_loc⊆P_global`, where `P_global` is the convex hull of all one-color heavy-plus-fluid configurations. Thus the scaled heavy **type** marginals and fluid means would all be exact. The coefficient cannot be increased beyond `4/5` in this mixed class, in the limiting strict-heavy four-vertex witness of `bipartite_mixed_fluid_sharpness_audit.md`.

## Step 1: live variables at an extreme local point form a forest

Fix an extreme point `(x,y)` of `P_loc`. Keep every fluid edge with `y_e>0` as a live column `e_u+e_v` in the vertex-capacity matrix. For each heavy pair `p`, let `s_p` be its number of positive type coordinates and let `rho_p=1` if its categorical inequality is tight, zero otherwise.

There can be at most one effective degree of freedom in a heavy pair. If `s_p-rho_p≥2`, there is a nonzero perturbation of its positive type probabilities preserving its active categorical sum (if any) and its weighted load at both endpoints. Indeed, the two endpoint weighted-load rows are identical up to their vertex positions because every type of `p` has the same endpoints; they impose just one scalar weighted-sum equation. Small perturbations in both directions preserve all other active rows and nonnegativity, contradicting extremality. Thus `s_p-rho_p≤1`.

If `s_p-rho_p=0`, the pair is deterministic: either no type is present or one type has probability one. If `s_p-rho_p=1`, it has exactly two possible categorical states: none versus one positive type (`s=1,rho=0`), or two positive types summing to one (`s=2,rho=1`). After eliminating its categorical row, its live column in the vertex-capacity matrix is `c_p(e_u+e_v)`, where `c_p=w_h` in the first case and `c_p=w_{h_1}-w_{h_2}` in the second. If `c_p=0`, another two-sided perturbation contradicts extremality; hence every live coefficient is nonzero.

The live columns, consisting of positive fluid edges and live heavy pairs, must be linearly independent: any kernel vector yields a two-sided small perturbation of all positive fluid amounts and positive heavy state probabilities while preserving all active local rows. Because the combined support is bipartite, every cycle is even, and its alternating incidence relation gives a kernel vector among the corresponding columns after dividing by their nonzero scalar coefficients. Therefore the graph of live fluid edges plus live heavy pairs is a **forest** (in particular it has no parallel live two-cycle).

Let `C_1,...,C_k` be the connected components of the positive-fluid support, including singleton vertices incident to positive heavy variables when convenient. No live heavy pair can have both endpoints in one `C_i`, since its edge plus a fluid path would form a cycle. Contract each `C_i`; the live heavy-pair links form a forest. Heavy pairs in deterministic full states may connect components or lie inside one; they are not live columns and need no stochastic gluing in the next step.

## Step 2: private-component full-law additive estimate

Fix a positive-fluid component `C`. For every deterministic heavy pair touching `C`, fix its heavy state at the value specified by the extreme point; this subtracts a fixed nonnegative load from its endpoint capacities. Every remaining live heavy pair incident to `C` has its other endpoint outside `C`, so, **from C's viewpoint**, it is a private categorical guard attached to one fluid vertex. The live heavy support is a matching, so distinct guards touch distinct fluid vertices. The restricted local point `(x_C,y_C)` is feasible in the corresponding private-guard local polytope with those baseline capacities.

We need the following additive form of the private-guard lemma, including fixed baseline capacities `c_v∈[0,1]`: for every nonnegative fluid profit vector `q` on `C`, there exists a full-marginal categorical guard law such that

`E F_{C,q}(R) ≥ q·y_C-F_{C,q}(1)/4`.  (A)

In fact the law may be chosen independently of `q`. To verify (A), decompose `(x_C,y_C)` into vertices of its private local polytope. At each such vertex, **temporarily restrict fluid recourse to that vertex's positive-fluid support** `S_j`. This support may have several components even when the original `C` is connected. On one such component let `m` be its number of positive fluid edges, `n` its vertices, and `s_v-rho_v` the effective categorical freedom at guard `v`. The same active-row count as in `private_single_guard_arbitrary_fluid_five_fourths_candidate.md` gives `Σ(s_v-rho_v)≤n-m≤1`. Thus at most one guard's residual capacity varies there, between two values `a,b∈[0,1]` with probabilities `p,1-p`. Its restricted recourse as a function of that one capacity is monotone and `L`-Lipschitz, where `L` is the largest incident fluid profit and `L≤F_{C,q}(1)`. Its two-state Jensen loss relative to recourse at the mean capacities is at most `p(1-p)|b-a|L`. Summing this bound over disjoint components of `S_j` costs at most `F_{S_j,q}(1)/4≤F_{C,q}(1)/4`, because the unrestricted full-unit recourse on `C` can reproduce every configuration on `S_j`. The mean-capacity recourse on `S_j` is at least the local fluid profit `q·y^j`. Finally the actual full-`C` recourse is at least the restricted `S_j` recourse in every heavy state. Average the local-polytope vertex decomposition to obtain (A) with exact original guard-type marginals.

Fixed deterministic heavy pairs stay fixed throughout this full-marginal law, even if they join two fluid components. The only randomized pair states are live links, with categorical marginals exactly `x_h` on each endpoint's component law.

## Step 3: glue the full laws and use one global empty-heavy coin

For each positive-fluid component choose the q-independent full-marginal law from (A), retaining its joint distribution of all incident live heavy-pair states. On the contracted forest of live links, these component laws have the same marginal distribution on each shared categorical link: the original global `x_h` (and none probability `1-Σ_h x_h`). A standard tree gluing constructs a joint law preserving every component distribution: root each contracted tree, sample its root component, then sample each child component conditional on the already sampled state of its parent link, recursively. Zero-probability conditional states are irrelevant. Deterministic heavy links require no gluing because their state is fixed in every component law.

The resulting full heavy law is globally feasible because heavy simple support is a matching. Its type marginals equal the original `x_h`, and every fluid component retains its local residual-capacity distribution. Since recourse on the positive-fluid support decomposes over those components, (A) sums to

`E F_q(R_full) ≥ q·y-(1/4)Σ_C F_{C,q}(1)`.  (B)

Now use **one common global coin**: with probability `4/5` take this full heavy law; with probability `1/5` select no heavy edge. In the empty-heavy state the fluid recourse on the positive support is `Σ_C F_{C,q}(1)`. Hence the mixed heavy law has exact type marginals `(4/5)x_h` and

`E F_q(R_mix) ≥ (4/5)q·y`.  (C)

This is the place where a separate empty/full coin for each component would be unsafe: a deterministic full-state heavy pair linking two components must be synchronized globally. The one global coin handles every deterministic pair, while tree gluing handles only the genuinely fractional links.

For fixed heavy type marginals, the set of feasible **mean** fluid vectors is compact, convex, and downward closed. Inequality (C) for all `q≥0` is its support-function criterion for containing `(4/5)y`; downward thinning achieves exact equality. Thus the scaled extreme point lies in `P_global`. Decompose an arbitrary local point into extreme points, scale and mix their global laws. This would prove the stated inclusion.

## Audit boundaries

The forest argument uses bipartiteness of the **combined** support and matching simple support of heavy pairs. Without bipartiteness, odd live cycles need not yield a kernel. Without matching heavy support, two heavy pairs can compete at a vertex, the local categorical constraints and gluing cease to have this form. The proof uses uncapped divisible fluid; it does not imply an integer physical-edge coloring bound, nor does it incorporate per-edge recourse caps required by some rounding transfers.

There is a narrower exact bridge to **repeatable integer count patterns** when every small edge has one common weight `s` and the combined graph is bipartite. Put `k=floor(1/s)`. After selecting heavy type `h`, the maximum number of small edges at either endpoint is the integer `K_h=floor((1-w_h)/s)`. Normalize small counts by `k` and assign this heavy type effective fluid-model cost `H_h=(k-K_h)/k`. At a vertex, the exact local count hull has categorical heavy state plus mean small count bounded by the corresponding mean `K_h`; this is the local polytope above with costs `H_h`. For each one-color heavy state in the `4/5` fluid transfer, multiply fluid amounts by `k`. The resulting fractional bipartite `b`-matching has **integer** vertex capacities `K_h` (or `k` when no heavy type is selected). The bipartite incidence matrix is totally unimodular, so it decomposes into integer small-edge count vectors without changing its mean. Thus the same `4/5` inclusion holds for unbounded repeatable count patterns with a single uniform small weight. It does **not** assign distinct physical small-edge identities or prove a uniform integer palette bound; finite stock and per-edge caps need a separate transfer.
