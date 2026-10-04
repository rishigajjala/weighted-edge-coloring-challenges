# Sparsify–localize–type bridge for matching-heavy bipartite support

**Research candidate, 2026-10-03. Not an unrestricted theorem claim.** This note assembles an apparent `4/3+epsilon` physical coloring route for bipartite combined support with heavy simple support a matching, arbitrary parallel heavy categories, and arbitrarily tiny physical edges. It bypasses the unproved radius-one reciprocal rule. A full independent audit of the type-label lemma, forest localization, and finite-palette rounding interface is still needed before claiming the scoped result. The general-heavy-support and nonbipartite cases remain outside the route.

The key quantifier is to average over a random sparsified support **within each color**, not sample one support per color. An edge with vanishingly small normalized target may be sampled very rarely; per-color sampling would violate the physical edge-relative cap. Within-color averaging restores that cap exactly.

## One-color normalized setup

Let `alpha=3/4`. Contract every matched heavy pair to one supervertex, leaving bare vertices as singleton supervertices. A physical vertex `v` has pseudo-heavy normalized load `1-D_v`; both endpoints of a matched pair have the same `D_P`. Let `y_e>=0` be normalized tiny bundle targets, after aggregating parallel physical tiny edges with the same endpoint ports, with `sum_(e at v)y_e<=D_v<=1`. We ultimately split a bundle flow among physical edges proportional to their weights.

The actual categorical pseudo-heavy state at pair `P` gives real residual `R_P in [0,1]`, shared by its two physical endpoints. Its mean `p_P^act=E R_P` is at least `p_P=1/4+3D_P/4`; equality holds for the ideal alpha-scaled heavy law. This inequality accommodates bucket symbols rounded downward in the finite-field palette. Bare vertices have residual one.

Fix small `eta>0`, then much smaller sparsification scale `a>0` (`a<<eta²`). For each bundle independently, retain a target `y_e` deterministically if `y_e>=a`; if `y_e<a`, retain target `a` with probability `y_e/a` and zero otherwise. Call the random target `Y_e`, so `E Y_e=y_e`. At a vertex `v`, deterministic strong target is fixed, weak increments are independent, each at most `a`, their total variance is at most `a`, and `E sum_(e at v)Y_e<=D_v`.

Delete every retained bundle touching a physical vertex whose sampled total target exceeds `D_v+eta`. Write `Y_e^pr` for the retained target and `\widetilde Y_e=Y_e^pr/(1+eta)`. Every resulting physical vertex has `sum \widetilde Y_e<=(D_v+eta)/(1+eta)=:D'_v<=1`. In a matched pair use the common `D'_P`; its two ports obey the same upper bound. For each bundle, conditioning on its being sampled leaves independent weak increments at its endpoints with conditional mean at most `D_v-y_e+a` and variance at most `a`. Bernstein's inequality therefore gives, for `a<=eta/2`,

`E Y_e^pr >= (1-delta_pr)y_e`, with `delta_pr<=2 exp(-c eta²/a)`

for an absolute `c>0` (the two endpoint failures are union-bounded). For example, if `eta<=1` and `a<=eta/2`, the conditional deviation margin is at least `eta/2`; Bernstein with variance at most `a` and increment bound `a` permits `c=3/32`. This remains valid for deterministic strong bundles. The pruned support has physical degree at most `(1+eta)/a`, and pair-contracted degree at most `2(1+eta)/a`, because every retained weak bundle has target `a` and every retained strong bundle has target at least `a`.

## Local capped policy for each sampled support

Put `p'_P=1/4+3D'_P/4`. For a pair with actual residual `R_P`, independently across pairs first sample a shared bit `A_P|R_P ~ Bernoulli(R_P)`, so `P(A_P=1)=p_P^act>=p_P`. Couple it to a bit `A'_P~Bernoulli(p'_P)` with

`P(A'_P=1,A_P=0) <= (p'_P-p_P^act)_+ <= p'_P-p_P <= 3eta/4`.

If `p_P^act>p'_P`, thin `A_P`; if smaller, augment its off states. This coupling is per pair, hence the `A'_P` are independent with prescribed marginals. Bare vertices have `A=A'=1`.

For a fixed pruned support and its target `\widetilde Y`, decompose `\widetilde Y` into forest extreme points `y^k` of the unbounded bipartite degree polytope at the fixed `D'`. In each forest, root its trees and delete one uniformly selected residue class of edge depth modulo a fixed integer `J`. Every surviving component has physical diameter at most `2J` and, because of the sparsified degree bound, contains at most a fixed `B=B(a,J)` pair IDs. Apply the capped independent-activation/paired-residual forest theorem with caps `12y^k_e` separately to each retained forest. Averaging forest and residue choices preserves a coordinatewise mean at least

`alpha(1-1/J) \widetilde Y_e`, with pointwise **averaged** edge cap at most `12\widetilde Y_e`. An individual forest term may have a larger edge cap `12y^k_e`; only its vertex sum and the averaged edge cap are used below.

For each local component term, first construct a q-independent feasible policy `Z_e(A')` by support-function separation. It depends only on activation bits of pair IDs in that component. Convert it to a real-residual policy by taking the conditional expectation of `Z_e(A')` times the indicator that both probe endpoint bits `A` equal one, given the actual categorical heavy states. In every realization before this last average, a physical vertex with `A_v=0` carries no tiny flow, while one with `A_v=1` carries at most one unit. Thus after averaging the tiny load at that vertex is at most `P(A_v=1|R)=R_v`; feasibility under the actual residual is pointwise. A forest term has edge cap `12y^k_e`, and averaging the forest terms restores cap `12\widetilde Y_e`.

After forest averaging, an edge's cap is `12\widetilde Y_e`; the augmentation event is independent of the chosen forest/residue. Thus its expected loss is at most `12\widetilde Y_e` times the probability that one endpoint is augmented-only (`A'=1,A=0`). The two endpoint probabilities give a loss at most `18eta\widetilde Y_e`. Hence the local policy's product-heavy-state mean is at least

`[alpha(1-1/J)-18eta]\widetilde Y_e`.

The forest decomposition and rooted residues may depend on the entire fixed sampled support; that is harmless. For each chosen component term, **state dependence** is confined to its at most `B` pair IDs. For an edge incident to supervertex `P`, all those IDs lie in the sampled pair-graph ball `B_r(P)` with `r=2J+2`.

## Finite type labels with rare local collisions

This is the label lemma being audited separately. For the *unpruned* sampled pair graph define a symmetric matrix `T` on supervertices: `T_PQ` is the sum of sampling probabilities of external bundles joining `P,Q` (diagonal internal bundles may be omitted). Since each supervertex has two ports of normalized target degree at most one, every row and column sum of `T` is at most `K=2/a`. Put `W=I+T+...+T^r` and `S=sum_(l=0)^r K^l`; all `W` row/column sums are at most `S`.

Call an entry `W_PA>gamma` strong. The strong-entry graph has maximum degree at most `S/gamma`. Properly color its square with a bounded number of base types. Thus for any root `P`, two distinct IDs `A,B` both strong from `P` have different base types. Independently give every supervertex one of `Q` sublabels. For each row `(P,base type,subtype)`, apply the manuscript's Harris–Srinivasan many-sums proposition to the additive weak-label load `sum_{A:base(A)=base,W_PA<=gamma} W_PA 1{sub(A)=subtype}`. Its mean is at most `S/Q`, each source coefficient at most `gamma`, and one source contributes total weight at most `S` over all rows. Choosing `Q` large and then `gamma` small gives a deterministic sublabel assignment for which every weak final-label load is at most `xi`, with `xi` arbitrarily small and independent of graph order.

For every root `P`, strong–strong same-final-type pairs are absent, and the ordered weight of strong–weak or weak–weak same-final-type pairs is at most `2xi S`:

`sum_(A!=B, type(A)=type(B)) W_PA W_PB <= 2xi S`.

If the sampled radius-`r` ball at `P` has two IDs of one final type, take a breadth-first spanning tree of that ball and its two root paths. Their union is a Y-shaped tree with a common trunk and edge-disjoint arms. The probability of each embedded tree is the product of its distinct sampling probabilities. Sum over trunks and arms; allowing all matrix walks only increases the sum. The bound above then gives

`Pr{B_r(P) has a repeated final type} <= 2xi S²`.

Indeed, the trunk length is summed by `W`, whose row sum is at most `S`, and the two arm lengths are already summed inside the displayed same-label `W` product. This uses tree witnesses rather than multiplying probabilities of overlapping paths. Pruning only removes sampled edges, so the same upper bound controls local components of the pruned graph. Denote the uniform bound by `delta_col`, chosen as small as desired.

For a fixed sampled support and component term, discard its tiny flow if its participating pair IDs have repeated final type. This only deletes flow and keeps feasibility. If the ball `B_r(P)` is good, no term on an edge incident to `P` is discarded. In each forest term, the sum of **edge caps** at a physical port is at most `12 sum_e y^k_e<=12`; this remains true after averaging forests. Therefore the total product-law marginal flow lost at that port from collision deletion is at most `12 delta_col` after averaging over sampled supports. This is a *vertex aggregate* loss, not a coordinatewise relative loss; rare individual edges can lose all their marginal.

The pre-collision coordinate mean after support averaging is at least

`beta_0 y_e`, where `beta_0=(1-delta_pr)[alpha(1-1/J)-18eta]/(1+eta)`.

Choose a small marking threshold `theta>0`; mark any bundle whose collision deletion loses more than `theta y_e`. Then the total normalized target of marked bundles at every physical vertex is at most `12 delta_col/theta`. Every unmarked bundle has product-law mean at least `beta y_e`, with `beta=beta_0-theta>0`. All small parameters can be chosen so `beta` is arbitrarily close to `3/4`.

Finally average the collision-deleted local policy over **all** sampled supports inside each color. Convexity preserves per-color residual feasibility. Its cap is edge-relative:

`z_e <= E_S[12\widetilde Y_e] <= 12 y_e/(1+eta)`.

This is the crucial bound uniform in the smallest positive `y_e`.

## Exact finite-field blocks and physical palette

Use the pseudo-heavy buckets and `3tau` row slack of `bounded_heavy_pairs_integer_transfer_candidate.md`. Let `s=1-3tau`, choose `J,eta,a,theta,delta_col` to make `beta>3/4-epsilon_0`, and choose the normalized tiny target for a main palette of `M` colors as

`y_e=(1+delta)w_e/(beta s M)`.

Give each physical pseudo-heavy identity normalized marginal `1/(alpha M)` before alpha transfer. The ideal alpha-scaled categorical law puts each identity in a color with probability `1/M`. At a vertex with original heavy weight sum `H`, heavy count `h<=N`, and tiny stock `t`, the rounded pseudo-heavy contribution is at most `(H+eta_h h)/(alpha s M)`, where `eta_h` is the heavy-bucket width. Since `beta<alpha`, total local target load is at most `[N+(eta_h+delta)N]/(beta s M)`. Thus choose `rho>eta_h+delta` and `M >=(1+rho)N/(beta s)`. Choose `M` a multiple of the block size below and large enough that the physical per-color tiny cap `12s y_e/(1+eta)` is at most `w_e`.

The type count is bounded *a priori* by a function of `K,r,gamma,Q`, for example `T_0<=Q[(S/gamma+1)^2+1]`; it does not depend on `M`, `N`, or graph order. Let `K_b` be the fixed heavy-bucket count. Choose a prime power `q>T_0` and `q` large relative to `K_b/epsilon_heavy` **before** setting `M`. Let `d>=B` and block length `L=q^d`, then set `M=L ceil((1+rho)N/(beta s L))`. After requiring `N>=L` and choosing parameters so `(1+rho)/(beta s)<2`, one has `M<=3N`, whence `K_b M/q<=3K_b N/q<=epsilon_heavy N`. For each type choose a distinct Vandermonde linear form `ell_type:F_q^d->F_q`; every at most `B` distinct forms are independent. For every heavy pair `P` and bucket `b`, assign `m_(P,b)=floor(q n_(P,b)/M)` symbols to bucket `b`, with remaining symbols empty. In each block index colors by `x in F_q^d`, and let `P` read `ell_type(P)(x)+shift_P` for any fixed shift. Every bucket then appears exactly `M m_(P,b)/q<=n_(P,b)` times across the `M` main colors. Assign distinct physical heavy identities to these slots. At most `K_b M/q` identities per pair remain, and the heavy simple matching lets all pairs share that many heavy-only extra colors.

The actual rounded-down bucket law has residual mean at least the ideal `p_P`; the `A`/`A'` coupling above still loses at most `3eta/4` per pair. For any fixed sampled support and surviving local component term, at most `B` pair IDs enter its heavy-state function, and collision deletion guarantees their final types are distinct. The `L` colors in a block therefore enumerate their **exact independent product categorical law** for that arbitrary local function, regardless of shifts. Averaging first over each support/component term and then over blocks gives every unmarked physical tiny edge total fractional coverage at least `M*s*beta*y_e=(1+delta)w_e`.

Scale each unmarked edge's color fractions down to sum exactly `w_e`, retaining every vertex/color fractional capacity. The pseudo-heavy construction leaves `3tau` free in any vertex/color row with positive tiny options, and the physical tiny cap is at most its own weight for large `M`. The manuscript's two-endpoint option rounding then selects one whole color for each unmarked physical tiny edge while increasing any row by at most `2tau`. The marked bundles have total physical tiny stock at each vertex at most `Delta_mark=(beta s M/(1+delta))*(12delta_col/theta)=O(delta_col N/theta)`. They fit in `ceil(Delta_mark/(1-2tau))` extra colors: give each marked physical tiny edge the uniform option distribution on these colors, so each vertex/color expected load is at most `1-2tau`, and apply the same two-endpoint option lemma. Together with the leftover-heavy palette, this yields the scoped candidate count `(4/3+epsilon)N+O_epsilon(1)` for sufficiently small `tau` and large `N`, uniformly in graph order and smallest positive tiny weight.

## Explicit pending audits

1. Check the type-label theorem's HS normalization and the Y-tree union bound with all edge-depth conventions, including parallel sampled bundles and internal pair bundles. The `2xi S²` display hides a fixed `r` factor, not a graph-size factor.
2. Check the forest localization's q-independent coordinate policy and its exact pair-state locality after cap-concavity averaging. Each *term* is local even if the final averaged function has unbounded global support.
3. Check the pseudo-heavy rounding interface carefully: scaling by `s` alone does not create a uniform `2tau` margin beside heavy weights near one; the upward buckets and `w''=min(1,bar w/s)` are essential.
4. Use a physical-row additive bound when marking edges. No coordinatewise small collision probability is asserted for rare edges; the argument needs only bounded total marked stock at each vertex.
5. Preserve the parameter order: desired final error; forest depth `J`; pruning `eta`; sampling scale `a<<eta²`; type accuracy via `Q` then `gamma`; an a priori final-label bound; field size `q`; block length `L=q^B`; and finally `N` large relative to `L`. Only then define `M` by rounding up to a block multiple and compute the normalized target `y`. None of these fixed parameters may depend on graph order or the smallest positive edge weight.
