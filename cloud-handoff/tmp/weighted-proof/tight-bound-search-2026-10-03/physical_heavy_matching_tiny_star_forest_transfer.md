# Physical heavy-matching plus tiny-star-forest transfer

**Status: proved fractional-colouring theorem.** Let `G` be a finite loopless weighted multigraph. Every physical edge is either heavy, of weight greater than `1/2`, or tiny, of weight at most `τ`, where `0≤τ<1/2`. Assume the simple support of the heavy edges is a matching and the simple support of the tiny edges is a star forest. Parallel physical edges and mixed weights within a bundle are allowed. If the incident physical edges at every vertex can be packed into `N` unit bins, then

`χ_f,w(G) ≤ [(3/2−τ)/(1−2τ)]N = [3/2+2τ/(1−2τ)]N`.       (1)

More exactly, there is a probability distribution on **actual physical-edge subsets** feasible in one global colour in which each physical edge is present with probability `1/{[(3/2−τ)/(1−2τ)]N}`. No copies of one physical edge are introduced. For `N=1`, all edges together fit at every vertex and the assertion is immediate. Below assume `N≥2` and pad every local packing to exactly `N` bins. The theorem is about fractional colouring; it does not by itself supply a uniform integer-colouring error. For `τ≤1/6`, (1) also implies the simpler bound `(3/2+3τ)N`.

## 1. Full source states from actual local bins

For each heavy-support pair `uv`, choose a heavy identity `J_uv`: each physical heavy edge on `uv` is chosen with probability `1/N`, and the empty identity has the remaining probability. This is a common law at both endpoints, since every heavy occurrence appears once in each local `N`-bin packing and no other heavy bundle meets either endpoint. The associated common residual capacity is `R=1-w(J_uv)` if a heavy edge is chosen and `R=1` if `J_uv` is empty.

Conditional on `J_uv`, independently choose at `u` and `v` an empirical local-bin tiny subset from bins having that heavy identity in their respective local packings. At a vertex outside the heavy support choose a uniformly random local bin's tiny subset. Call the heavy identity together with both endpoint tiny subsets a **source state**. Before the star coupling, sample different heavy-pair source states independently; sample fixed-vertex states independently as well. Every physical tiny edge is included in its own vertex's sampled subset with probability exactly `1/N`. Every sampled endpoint tiny subset has total weight at most that endpoint's state residual. The independent conditional choices at a heavy pair are only a convenient joint law: each endpoint's exact conditional local-bin law is preserved.

Orient every nontrivial tiny-star component from a chosen hub to its leaves. Only the tiny subset chosen at a **leaf** is used to propose its incident tiny edges; the hub's sampled tiny subset is not needed. For a leaf `a`, let `Z_a` be the total weight of its proposed subset. Then `0≤Z_a≤R_a≤1`, and each incident physical tiny edge has proposal probability `1/N`.

## 2. Scalar coupling at each hub

Fix a tiny-star hub `o`, with residual `X=R_o`. A heavy pair can have both endpoints as leaves of this star, or can join `o` to one leaf. In the first case the pair's whole source state is private to this star; its two proposed leaf loads combine into one variable `Y_i=Z_a+Z_b∈[0,2]` with a prescribed marginal law. In the second case, call the partner leaf's load `Z_*`; it satisfies `Z_*≤X` statewise. Sample that pair source state in the initial independent stage.

Every other proposed leaf load is a **singleton** source. Its heavy pair has at most one endpoint among the leaves of this star; if it has the hub as its other endpoint, it is the own-partner case just handled. Hence singleton loads come from distinct initially independent source states. Let `S` sum them. If there is an own-partner leaf put `B=1-X+Z_*`; otherwise put `B=1-X`. In either case `B∈[0,1]` and is independent of all singleton loads. Thus `U=B+S` is a sum of independent `[0,1]` variables.

The expected total proposed tiny load at `o` is exactly `N^{-1}` times the total weight of its incident physical tiny edges, because every proposal is driven by its leaf's local-bin marginal. At the hub's original local bins, tiny load never exceeds residual capacity. Therefore

`E U+Σ_i E Y_i = 1-E X+E(total proposed tiny load at o) ≤1`.

Apply the independent-base/private-sum lemma of `upper_arbitrary_paired_star_forest_half_deficit.md`. It couples the private `Y_i` to the independent base while preserving their individual laws and the full joint law of all base summands, with

`E(total proposed tiny load at o−X)_+ ≤1/2`.             (2)

Lift the resulting load coupling to full source states using the original conditional law of each source state given its load value. In particular, all physical-edge subset marginals and heavy-identity laws are preserved. A private pair belongs to just one tiny-star component. Conditional on all initially sampled cross-component and own-partner source states, draw the private source states of different stars from their respective coupling kernels. Since the base law in (2) is unchanged, these kernels are globally consistent even when heavy pairs link the tiny stars in cycles.

## 3. Trim proposals and record physical-edge deficits

In each realized tiny star, keep the heavy edge (if any) and delete proposed tiny edges at the hub until its tiny load is at most `X`. Deleting never hurts leaf feasibility. If the initial overload is `δ=(W-X)_+`, the total deleted weight `D` obeys `D≤δ+τ`: immediately before the last deletion the hub was still overloaded, and that last edge weighs at most `τ`. By (2), `E D≤1/2+τ`.

Let `t_e` be the inclusion probability of a tiny physical edge in this normal feasible pattern, and put `d_e=1/N−t_e`. Then `0≤d_e≤1/N`. At every hub, `Σ_(e incident v)w_e d_e=E D≤1/2+τ`; at a leaf its deleted weight is at most its hub's `D`, so the same inequality holds. Isolated tiny vertices have zero deficit. Each heavy physical edge retains probability exactly `1/N`.

## 4. An actual-edge correction law

Set `c=(1/2+τ)/(1−2τ)`, so `c≥1/2`. Put `p_e=d_e/c` for each tiny physical edge. As `N≥2`, `p_e≤1/(cN)≤1`. At every vertex,

`Σ_(e incident v)w_e p_e ≤ (1/2+τ)/c = 1−2τ`.         (3)

There is a distribution on feasible **binary** tiny-edge selections with exact marginals `p_e`. Here is an elementary rounding proof. Start with the fractional vector `p`. Keep the weighted-degree equality at every vertex incident to at least three currently fractional edges, and drop a vertex row once at most two of its incident variables remain fractional. If `F` is the set of fractional edges and `A` the active rows, every row of `A` touches at least three members of `F`, while each edge touches at most two rows, so `3|A|≤2|F|<3|F|`. There is a nonzero nullspace direction on `F` preserving every active weighted degree. Move in each direction until a coordinate reaches zero or one, and choose between the two endpoints with probabilities that preserve the current vector in expectation. Repeat; at least one coordinate becomes integral each step. Every marginal remains `p_e`. A dropped vertex had at most two fractional incident edges at the time of dropping, so its final weighted load can rise by at most `2τ` above its load then. Its load until dropping equals the initial mean in (3). Thus every final selection has vertex load at most one.

Use the normal heavy-plus-tiny pattern with probability `1/(1+c)`. With probability `c/(1+c)`, choose an all-heavy-empty tiny correction pattern from the rounding law. A heavy physical edge then has probability `1/[(1+c)N]`; a tiny edge has probability

`[t_e+c p_e]/(1+c)=[t_e+d_e]/(1+c)=1/[(1+c)N]`.

Multiplying this pattern distribution by `(1+c)N=[(3/2−τ)/(1−2τ)]N` gives a fractional colouring covering each actual physical edge exactly once. This proves (1).

## Scope and boundary

The star-forest assumption is used once: every tiny edge has a designated leaf endpoint, and trimming at one hub controls each leaf's loss. The heavy matching assumption is used to create a single common residual source per heavy pair; with two heavy bundles meeting a vertex, its local heavy identity is no longer a one-pair source. Arbitrary heavy-pair links among different tiny stars are permitted. The result gives a physical-edge fractional distribution, stronger than a repeatable-count pattern statement, but an integer colouring with a graph-size-independent additive term requires an additional rounding argument.

## Bipartite combined support: the `1/e` deficit

Suppose in addition that the **combined heavy-plus-tiny simple support is bipartite**. A heavy pair cannot join two leaves of one tiny star, since that heavy edge and their two tiny spokes would form a triangle. Thus the private variables `Y_i` in Section 2 are absent. The own-partner heavy pair, if present, is absorbed into `B=1-X+Z_*` exactly as before. The other singleton leaf loads sum to `S`, a sum of independent `[0,1]` variables independent of `H=X-Z_*` (or `H=X` when there is no own-partner leaf). Mean feasibility gives `μ=E S≤r=E H≤1`.

The elementary independent-capacity estimate from `upper_arbitrary_paired_star_forest_half_deficit.md` gives

`E(S-H)_+ ≤ μ-r+r exp(−μ) ≤ μ exp(−μ) ≤1/e`.       (4)

For completeness, `min(H,S)≥H min(1,S)` pointwise for `H∈[0,1]`, while independence and the independent bounded-summand inequality give `E min(1,S)≥1−exp(−μ)`. Hence `E(S-H)_+=μ−E min(H,S)≤μ−r(1−exp(−μ))`, proving (4). There are no private couplings to arrange; sample all heavy-pair source states independently, including any pairs linking different tiny stars. Actual-edge trimming adds at most `τ`, so every vertex's weighted tiny-edge deficit is at most `1/e+τ`.

Set `c_b=(1/e+τ)/(1−2τ)` for `0≤τ<1/2`. For `N≥3`, the correction marginal `p_e=d_e/c_b` lies in `[0,1]`, because `d_e≤1/N` and `c_b≥1/e>1/3`. Its mean weighted degree is at most `(1/e+τ)/c_b=1−2τ`. The same floating-variable rounding of Section 4 gives an actual-edge correction law of load at most one. Mixing it with the normal bipartite pattern yields exact probability `1/[(1+c_b)N]` for every physical edge, and therefore

`χ_f,w(G) ≤ [1+(1/e+τ)/(1−2τ)]N`, `N≥3`.         (5)

For `N=1`, the entire physical edge set is one feasible colour. Formula (5) is stated only for `N≥3`; no special claim is made here for `N=2`. Its coefficient tends to `1+1/e` as `τ↓0`. Bipartiteness refers to the combined support, not merely to the tiny star forest.

## Sharpness of the general `3/2` limit

The leading `3/2` coefficient in (1) cannot be lowered as `τ↓0`. Let `N` be even and `τ=1/k` for an integer `k≥3`. On vertices `u,v,z`, put `N/2` physical heavy edges of weight one on `uv`, and `Nk/2=N/(2τ)` physical tiny edges of weight `τ` on each of `uz` and `vz`. The heavy simple support is a matching and the tiny support is one two-spoke star.

At `u` and `v`, the heavy edges use `N/2` bins and their tiny spokes use the remaining `N/2` bins, exactly `k` tiny edges per bin. At `z`, all `Nk` tiny edges use exactly `N` bins. Hence the local benchmark is `bp(G)=N`. Every heavy-containing global colour blocks both spokes, while the tiny edges have total weight `N` at `z`. Thus heavy edges require `N/2` colour mass disjoint from at least `N` tiny-only colour mass, so `χ_f,w(G)≥3N/2`. The obvious packing attains equality, as does an integer colouring. This nonbipartite triangle is a sharpness witness only for the general coefficient.
