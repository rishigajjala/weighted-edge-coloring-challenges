# Independent audit: finite-stock tiny edges on stars

**Status.** I found no gap in the two arguments below under the stated hypotheses. These are restricted-support results for actual indivisible edges, not unrestricted weighted edge coloring. The number `N` and a feasible `N`-bin local packing at each vertex are mathematical inputs; the proof establishes existence and does not claim that finding optimal `bp=N` is efficient.

Assume every heavy physical edge has weight greater than `1/2`, heavy support is a matching of vertex pairs (parallel heavy edges allowed), every other edge has weight at most `tau<1/2`, and the tiny-edge support is a vertex-disjoint star forest. Every physical edge occurs once in each endpoint's `N`-bin histogram, where `N>=2` is a common feasible local bin count.

## Arbitrary star forest: exact fractional coloring

Use each physical heavy-edge identity as a shared state of its pair, with probability `1/N`; use the no-heavy state for the remaining slots. At the two endpoints, sample their tiny-edge source subsets conditionally on this state from their given histograms. This preserves both local histogram laws. Across different heavy pairs sample states independently. At each tiny star, use the leaf-side source for every tiny edge; hence every physical tiny edge has proposed probability exactly `1/N`. A hub's local histogram supplies only its residual capacity `X` and the mean inequality between that capacity and its incident tiny stock. If a heavy pair joins the hub to one of its leaves, the leaf's proposed load `Z_own` on their common tiny bundle obeys `Z_own<=X` in every state, since the selected heavy physical edge has the same weight at both endpoints.

For a fixed star, externally shared pair states remain independent. A private heavy pair joining two leaves supplies a joint source whose combined tiny load lies in `[0,2]`; a singleton leaf source lies in `[0,1]`. The proved scalar half-deficit transport lemma couples private sources conditional on the shared sources so that the hub's expected preliminary excess is at most `1/2`. Coupling source *loads* can be lifted by conditioning back to complete heavy identities and tiny subsets, so each pair's full law is preserved. An internal pair occurs in only this star, hence these conditional resamplings can be done for all stars without changing any cross-star pair law. This is the point at which finite-stock consistency would otherwise be lost.

In each sampled star, delete proposed tiny edges until its hub fits. If excess is `d>0`, the deleted total weight is less than `d+tau`, because the last deleted edge weighs at most `tau`. Thus every vertex loses expected tiny load at most `1/2+tau`: a hub directly, and a leaf no more than its hub because it belongs to only one star. Write `t_e<=1/N` for the probability that physical tiny edge `e` survives, and `d_e=1/N-t_e`. Then

`sum_{e tiny at v} w_e d_e <= 1/2+tau` for every `v`.

Set `c=(1/2+tau)/(1-2tau)`. The desired correction marginals `p_e=d_e/c` have weighted degree at most `1-2tau` and satisfy `p_e<=1` because `d_e<=1/N`, `N>=2`, and `c>=1/2`. They can be represented by a distribution on actual feasible tiny-edge subsets. To see this, start with the vector `p`. While fractional variables remain, preserve the weighted load row of each vertex incident with at least three fractional variables. If there are `m` fractional edge variables and `h` such active rows, `3h<=2m`, hence `h<m`; the active weighted incidence matrix has a nonzero null direction. Randomly move to one of the two maximal feasible endpoints of that direction, with probabilities preserving the current vector's expectation. At least one variable becomes integral. Once a vertex has at most two fractional incident variables, its subsequent load can increase by at most `2tau` from its load when that row stopped being preserved. Its final integer load is therefore at most one. This finite randomized rounding preserves every edge marginal exactly.

Mix the normal pattern with probability `1/(1+c)` and an empty-heavy correction tiny subset with probability `c/(1+c)`. Every physical heavy edge has marginal `1/[(1+c)N]`; every tiny edge has marginal `(t_e+d_e)/ (1+c)=1/[(1+c)N]`. Consequently the fractional chromatic number is at most

`(1+c)N = [(3/2-tau)/(1-2tau)]N`.

This argument gives a fractional coloring on **actual physical edges** and respects their once-per-edge stock. It does not by itself give an integer coloring with a uniform additive error, since the number of distinct physical edge types or generated patterns may grow with `N`.

## One tiny star: integer coloring by list permutation

Suppose the tiny support is one star. Keep each endpoint's actual `N` tiny-subset lists and align the two endpoints of each heavy pair by the common physical heavy-edge identity. Each heavy physical edge occurs in exactly one aligned slot, and every physical tiny edge occurs exactly once in its leaf's list. A private pair joining two leaves gives one list of combined tiny loads in `[0,2]`; all other leaf groups give lists in `[0,1]`. If the hub's heavy pair joins its own leaf, keep that leaf's tiny source with the hub: in each slot its load `Z_own` is at most the hub residual `X`, so `H=X-Z_own` lies in `[0,1]`. Otherwise put `H=X`.

Pair each new group list in reverse sorted order with the current aggregate list. If two lists have ranges at most `r` and `s`, their reverse pairing has range at most `max(r,s)`: for any two positions, the increase in one sorted list and decrease in the other have opposite signs. Iteration makes the aggregate `T` of non-own leaf groups have range at most `2`. Sort `T` and `H` in the same order. For `D=T-H`, any two positions differ by at most `max(range(T),range(H))<=2`, because the two sorted increments are nonnegative and are subtracted. The local hub histogram gives `mean(D)<=0`. A random variable of interval width at most `R` and nonpositive mean has positive-part mean at most `R/4`; therefore `sum_{j=1}^N(D_j)_+<=N/2`.

In each slot delete actual tiny edges greedily until the hub fits. The total deleted weight `W` is at most `(1/2+tau)N`. Each original slot is now a feasible whole-edge color, including all its heavy edges. The deleted edges form one tiny star; next-fit packs them into `q` additional whole-edge colors. Every closed next-fit bin has load greater than `1-tau`, so for `W>0`, `q-1<W/(1-tau)` and hence `q<=ceil(W/(1-tau))`; the same formula holds for `W=0`. Thus the total number of colors is at most

`N+ceil[(1/2+tau)N/(1-tau)] = ceil[3N/(2(1-tau))]`.

If the **combined original support is bipartite**, two leaves of this star cannot be joined by a heavy pair. Every non-own group then has range at most one, so `range(T),range(D)<=1`, `sum(D_j)_+<=N/4`, and `W<=(1/4+tau)N`. The integer bound improves to

`N+ceil[(1/4+tau)N/(1-tau)] = ceil[5N/(4(1-tau))]`.

The one-star proof is a deterministic existence construction from the local histograms (sorting and next-fit suffice once the histograms are provided). Its group permutations cannot be applied independently to several stars sharing a heavy-pair state; that is why the arbitrary-star-forest statement above is presently fractional rather than integer.
