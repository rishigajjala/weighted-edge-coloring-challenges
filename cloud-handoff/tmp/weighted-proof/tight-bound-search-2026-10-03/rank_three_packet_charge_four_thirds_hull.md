# A rank-three packet-charge four-thirds hull theorem

**Interim scoped result.** This is an asymptotic/fixed-support local-to-global configuration-hull inclusion for a bipartite graph class. It is not an exact finite-instance `chi<=ceil(4bp/3)` statement and not an unrestricted bound. No manuscript edit is proposed during the five-hour exploration protocol.

Let a fixed finite bipartite *typed* support have heavy edge types of weight greater than `1/2` and light edge types of weight at most `1/3`; there are no medium types. A type is an endpoint pair plus a common physical weight, and its nonnegative demand may be replicated. For each light type `e`, set `k_e=floor(1/w_e)>=3` and charge a physical copy `1/k_e`; charge a heavy copy `1`. Assume the following checkable local **heavy-bin charge condition**: whenever a feasible one-color local bin contains a heavy edge, the sum of light charges in that bin is at most `1/3`. A sufficient special case is that no feasible heavy-containing bin has two or more light edges.

For any feasible local bin containing only light edges, its total charge is at most `4/3`: since `w_e>1/(k_e+1)` and `k_e>=3`,

    1/k_e < ((k_e+1)/k_e) w_e <= (4/3) w_e.

The bin's total weight is at most one. A heavy-containing bin has charge at most `1+1/3=4/3` by hypothesis. Therefore every vertex-local feasible configuration `p` satisfies

    sum_{heavy e incident v} p_e
      + sum_{light e incident v} p_e/k_e <= 4/3.      (1)

The inequality extends by convexity to each local configuration hull.

Now let a rational demand vector `x` lie in the intersection of the vertex-local hulls. Choose large integers `N` so every `Nx_e` is integral. For each light type `e`, partition its `Nx_e` physical copies into `ceil(Nx_e/k_e)` packets, each of at most `k_e` parallel edges. Keep each heavy physical edge as a singleton packet. The resulting ordinary bipartite packet multigraph has maximum degree

    Delta_N <= (4/3)N + C,

where `C` is at most the maximum number of incident light types and does not depend on `N`. Indeed each light packet count is `Nx_e/k_e+O(1)`, and (1) bounds its fractional degree. By bipartite multigraph edge coloring, the packet graph has a proper coloring in `Delta_N` colors. Replace each colored light packet by its constituent parallel weighted edges. At a vertex a color contains at most one packet, so its light load is at most `k_e w_e<=1`; a heavy packet alone is also feasible. Thus all `Nx` physical edges are colored in `(4/3)N+O(1)` colors.

Divide by `N` and take a limit. The global repeatable-count configuration hull contains `3/4` of the intersection of the local configuration hulls on this fixed support. Equivalently the asymptotic local/global packing gap is at most `4/3` for all nonnegative demands and profits in this class. No topology restriction beyond bipartiteness appears: cycles, branches, parallel edges, and shared heavy endpoints are allowed.

The rank-three threshold is sharp for this charge argument. A light edge of rank two has `1/k=1/2` while its weight can approach `1/3`, so its charge/weight ratio can approach `3/2`. Also, a heavy edge can sometimes fit multiple light items of different ranks whose total charge exceeds `1/3`; for example weights near `0.67`, `0.251`, and `0.07` fit together and have charges `1+1/3+1/14>4/3`. Such a bin invalidates (1), but does **not** by itself produce a physical global lower bound above `4/3`. The additive `C` packet-rounding term likewise prevents the proof from asserting a uniform finite-instance coefficient without further work.
