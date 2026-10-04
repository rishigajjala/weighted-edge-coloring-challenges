# Arbitrary real shared-source lists: simultaneous overload transport

**Audited 2026-10-03.** This proves an exact-stock integer transport statement for arbitrary links between tiny-star components. It closes the shared-source permutation step left open in `shared_source_range_two_audit.md` at the level needed for an asymptotic `3/2` bound. It does **not** prove that the final shared-source load lists all have range at most two for arbitrary real data, and it does not address unrestricted weighted multigraphs.

## Source-list theorem

Fix `N>=1` colors and a finite set of hubs. Each *shared* source has `N` labelled states, each a vector in `[0,1]^2` supported at a fixed pair of distinct hubs; one permutation assigns its states bijectively to the colors, simultaneously at both endpoints. Each *private* source has `N` labelled scalar states supported at one hub, with state-list range at most two; one permutation assigns those states bijectively to the colors. There may be arbitrarily many sources and no assumption on the graph of shared sources. Write `L_vc` for resulting total load and `T_v=sum_c L_vc`, which is independent of the permutations. Assume `T_v<=N` for every hub. Then permutations exist such that

`sum_{c=1}^N (L_vc-1)_+ <= N/2 + 6 popcount(N)`

simultaneously for every hub. If `N` is a power of two, the sharper exact bound `N/2` holds. Here `popcount(N)` is the number of ones in its binary expansion; the additive term can be replaced by `6 floor(log_2 N)+6`. The theorem is constructive using polynomially many rational linear-algebra operations when state values are rational.

### Real two-sparse signing lemma

For any matrix `A` with at most two nonzero entries per column, all of magnitude at most one, and any `x^0 in [-1,1]^m`, there is `s in {-1,1}^m` with `|A(s-x^0)|<=2` coordinatewise. Start with all variables live. Preserve the initial value of every row with at least two live nonzeros while moving inside the cube and fixing one variable at a boundary per move. If `m` variables are live and `r` rows active, then `2r<=2m`. If `r<m`, there is a kernel direction for the active rows. If `r=m`, incidence counting forces every active row and every live column to have exactly two live incidences; round each live coordinate to its nearest sign. This changes each active row by at most two. A row released earlier had at most one live coordinate at release, so its eventual change is at most two. This proves the lemma. In the application `x^0=0`, so `|As|<=2`.

### Exact balancing inside a power-of-two block

Suppose every source has `K=2^h` states, with shared-state coordinates in `[0,1]` and each private list of range at most two. Pair the `K` states arbitrarily within each source. Each pair supplies one state to the left child and one to the right child. For every shared state-pair, its endpoint-coordinate differences form one column with at most two nonzeros of magnitude at most one. Apply the signing lemma to choose orientations of **all shared pairs at once**, making the left-minus-right hub-load difference at most two everywhere. Then process each private state-pair separately: its scalar difference has magnitude at most two; orient it opposite the current sign of the difference at its hub. If the current difference is in `[-2,2]`, the new one remains in `[-2,2]`. This preserves every source's exact half-size quota and both endpoints of every shared state. Recurse independently on the two child blocks down to two-color blocks. Every split has hub-load difference at most two.

For a fixed hub, let the `K`-block total be `T=K mu`. At any bottom two-color block, its total `S` obeys `S<=2 mu+2-4/K`, by iterating `T_child<=T_parent/2+1`; the pair load difference is at most two. For nonnegative pair loads `a,b` with `S=a+b` and `|a-b|<=2`,

`(a-1)_+ +(b-1)_+ <= S/2 +(S-4)_+/2`.

Indeed, when at most one load exceeds one, the left side is at most `S/2` by the difference bound; when both exceed one, it is `S-2`, which is at most `S/2+(S-4)_+/2`. Summing the `K/2` bottom pairs gives

`overload(block) <= T/2 +(T-K)_+/2`.

For `K=1`, this last inequality follows directly from `(T-1)_+<=T/2+(T-1)_+/2`. Thus it holds for every power-of-two block. If `T<=K`, it yields the exact half-total bound `overload(block)<=T/2<=K/2`.

### Exact-quota subset rounding and dyadic decomposition

For `R` remaining states in every source and an integer `0<K<R`, select exactly `K` states from **each** source so that at every hub the selected load differs from `K/R` times the current total by at most eight. Introduce variables `x_gi in [0,1]`, one for each state, initially `K/R`, and preserve each group equation `sum_i x_gi=K`. For a private source, subtract the minimum of its scalar list from each hub coefficient; the common baseline cancels because the group sum is fixed, leaving coefficients in `[0,2]`. Shared-source coefficients lie in `[0,1]`; each variable meets at most two hub rows.

Maintain as active only hub rows with at least five live variables. If `m` variables are live, there are at most `m/2` unfinished group equations: an integer-quota group cannot have exactly one fractional live variable. There are at most `2m/5` active hub rows by incidence counting. Thus fewer than `m` equations are being preserved, so a nonzero nullspace direction exists. Move until some variable reaches zero or one, freeze it, and repeat. A hub row is released with at most four live variables; its adjusted load still equals the initial target at release, and each live variable can subsequently change by at most one. Its final error is at most `4*2=8`. The exact group equations make the baseline cancellation valid for the original loads as well.

Decompose `N` by repeatedly selecting the largest power of two `K<=R` from the `R` remaining states using that rounding lemma; when `R` itself is a power of two, take all remaining states. This yields `L=popcount(N)` blocks. Fix a hub and set `mu=T_v/N<=1`. If a residual block has `R` states and load `T_R`, write `D_R=T_R-R mu`. Initially `D_N=0`. A nonfinal selection has load `T_K=(K/R)T_R+epsilon`, `|epsilon|<=8`; its residual has `R'=R-K<R/2` and deviation `D_R'=(R'/R)D_R-epsilon`. Hence `|D_R|<=16` throughout and every selected block satisfies `|T_K-K mu|<=24`; the final block does too. Since the blocks partition all states, their deviations `D_b=T_b-K_b mu` sum to zero.

Run the power-of-two balancing procedure independently inside each block, using the **same color block** at all sources. Its overload is at most `T_b/2+(T_b-K_b)_+/2`. Because `mu<=1`, `(T_b-K_b)_+<=D_b^+`. Also `|D_b|<=24` and `sum_b D_b=0`, so `sum_b D_b^+=(sum_b |D_b|)/2<=12L`. Summing over blocks gives `overload(v)<=T_v/2+6L<=N/2+6L`, simultaneously at every hub.

## Physical weighted-edge-coloring consequence

Let a weighted multigraph have heavy edges of weight `>1/2` whose **simple support is a matching**. Let all other edges have weight at most `tau<1/2`, with simple support a **vertex-disjoint star forest**; parallel physical edges are allowed. Let `N=bp(G)` be the maximum number of unit-capacity bins needed by the incident edge weights at any vertex. Then

`chi'_w(G) <= ceil((3N/2+6 popcount(N))/(1-tau))`.

If `N` is a power of two, the sharper bound is `chi'_w(G)<=ceil(3N/[2(1-tau)])`. For `N=0`, there are no edges and the conclusion is trivial. The algorithm uses supplied `N`-bin local packings and is polynomial in their physical input size; it does not claim that optimal local packings can be found in polynomial time.

Proof of transfer: align the `N` rows at the endpoints of each heavy pair by physical heavy-edge identity, bijecting the rows without heavy edge arbitrarily. A pair joining different tiny-star components is one shared source. Its complete aligned row state moves together at both endpoints; the hub contribution at each endpoint is the heavy weight if that endpoint is its star hub, or that endpoint leaf's complete proposed tiny-spoke load if it is a leaf. This contribution is in `[0,1]`. Every source touching at most one star is private to that star. A heavy pair joining two leaves of one star has a scalar hub-contribution list in `[0,2]`; a hub-to-own-leaf heavy pair has contribution at most one per row by the leaf's original local bin, and other private sources have range at most one. Pairs touching no star can be placed in the normal rows independently. All these sources preserve every physical heavy and tiny edge exactly once before trimming.

The total proposed hub load over the `N` rows is exactly the physical weighted degree of that hub, at most `N`. Apply the source-list theorem. At each star, in every overloaded normal row delete tiny spoke edges until the hub capacity is met. Leaves remain feasible because deletion only reduces their original local-row tiny load while the aligned heavy state stays fixed. Total deleted weight at a hub is at most its total overload plus at most `tau` per normal row, hence at most `N/2+6 popcount(N)+tau N`. Repack each star's deleted spokes by Next Fit; all star repair palettes overlay because the stars are vertex-disjoint. The number of repair colors is at most the ceiling of deleted weight divided by `1-tau`. Adding `N` normal colors and simplifying gives the displayed bound. For power-of-two `N`, use the exact half-overload source theorem instead.

This covers **all real aligned source-state loads and arbitrary cross-star heavy links** within the stated heavy-matching/tiny-star-forest class. The additive logarithmic term is independent of the number of vertices, edges, or star components. It does not settle unrestricted weighted-edge-coloring bounds (`1.62` bipartite and `1.999` general upper bounds versus `4/3` and `3/2` lower bounds in the broader problem).
