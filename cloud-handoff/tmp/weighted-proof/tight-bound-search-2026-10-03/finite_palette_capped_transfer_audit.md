# Finite-palette gap after capped physical one-color transfer

**Status (2026-10-03): open.** The capped independent-activation theorem and heavy matching transfer yield a physical one-color law with exact marginals. This note identifies the extra statement needed for a uniform integer coloring and records one plausible route and its unresolved dependence issue. No new integer bound is claimed.

## Exact deterministic target

Let `N` be the local bin count, `alpha=3/4`, and `s=1-3tau` for bipartite tiny support. Choose an integer palette size `M>=N/(alpha s)`. Assign every physical heavy edge to exactly one color, with at most one heavy edge from each matched pair in any color. Write `R_v(c)` for the resulting actual residual capacity. A sufficient finite-palette fractional tiny assignment consists of `z_(e,c)` satisfying

`0<=z_(e,c)<=w_e`, `sum_c z_(e,c)=w_e` for every physical tiny edge, and `sum_(e incident v) z_(e,c)<=R_v(c)-3tau` wherever tiny flow is positive.

The bipartite source-preserving iterative rounding argument in `physical_tiny_cap_rounding_route.md` would then assign every tiny physical edge to exactly one color with at most `3tau` load increase at each vertex/color, yielding an integer coloring. The cap can be made much smaller: with normalized target `y'_e=w_e/(alpha s M)`, the new one-color theorem permits normalized flow at most `12w_e/(alpha s M)`, hence actual physical load at most `12w_e/(alpha M)` in a color, an `O(1/N)` fraction of a physical edge. This is important for concentration but does not itself provide the finite table.

For a fixed heavy schedule `H`, let `P_c(H)` be the capped tiny-flow polytope in color `c` with its residual capacities. The exact tiny demands belong to `sum_c P_c(H)` if and only if, for every nonnegative profit vector `q`,

`sum_c F_q(R^c(H),C) >= sum_e q_e w_e`,

where `F_q` is capped bipartite recourse. A random exact heavy injection (each matched pair independently injects its physical heavy edges into the palette) gives the correct one-color categorical law. The capped transfer proves the displayed inequality **after expectation over injections**, for each fixed `q`. It does not produce one injection satisfying every `q` simultaneously.

## A logical gap witnessed by physical tiny bundles

The `N=M=4` example in `physical_tiny_cap_rounding_route.md` has local bin count four, physical fractional coloring mass four, and integer chromatic number five, even as the tiny weights tend to zero. Its 50/50 mixture of exact-heavy schedules has enough *expected* capped recourse for every profit direction to cover the three tiny bundle stocks, while neither schedule has a source-preserving four-color assignment. This shows that an expected support inequality cannot simply be derandomized by averaging. It does not test the target palette size `M≈4N/3`.

## Minimal caps and a possible concentration route

For the one-color theorem set `C_e=12y_e`, rather than the loose physical cap `w_e`. With target `y_e=w_e/N`, every conditional tiny flow satisfies `z_e<=12w_e/N`, and after physical scaling the corresponding inclusion fraction is at most `12s/N`. For independent one-color draws, a fixed edge's **fractional** total coverage across `M=Theta(N)` colors is a sum of bounded `O(1/N)` terms of mean one and thus concentrates on scale `N^(-1/2)`. The physical edge indicators themselves have Poisson-scale fluctuations and should not be rounded before forming the finite table.

There is room for a controlled surplus when the palette has a small extra factor. If `M>=(1+epsilon)N/(alpha s)` and `0<delta<=epsilon`, use pseudo-heavy marginals `x'_h=1/(alpha M)` and normalized tiny target `y'_e=(1+delta)w_e/(alpha s M)`. The pseudo-heavy load is at most `1/(1+epsilon)` times the original heavy load per local bin, and the tiny target is at most `(1+delta)/(1+epsilon)` times its original load, so the local vector remains feasible. The one-color law then has heavy marginal exactly `1/M` and physical tiny mean `(1+delta)w_e/M`, with cap `12y'_e=O(w_e/N)`. Across `M` colors, its expected tiny fractional coverage is `1+delta`; a uniform `o(1)` concentration bound could absorb the surplus before source-preserving rounding.

Two obstructions remain. First, independent color draws do not use each heavy physical edge exactly once; direct identity sampling misses a constant fraction of distinct identities. Grouping near-equal heavy weights into a bounded number of buckets could allow relabeling and `o(N)` residual heavy repair, but conditioning bucket counts creates cross-color dependence. Second, the support-function proof gives a conditional tiny-flow policy that may depend on heavy states throughout the graph. A color draw can therefore affect coverage rows for arbitrarily many distant tiny edges, so the manuscript's Harris--Srinivasan proposition does not immediately give simultaneous graph-order-independent concentration. A local or bounded-influence realization of the capped policy, or a direct exact-injection discrepancy theorem for all recourse profit directions, would close this route.

There is nonetheless a useful **fixed-profit concentration bound under exact heavy injections**. Normalize `q>=0` by `sum_e q_e w_e=1`, and for each heavy pair `P` define `a_P=sum_(e incident to an endpoint of P) q_e w_e`. Every tiny edge meets at most two heavy pairs, so `sum_P a_P<=2`. Use the minimal cap `C_e=12w_e/N` (or the corresponding `O(w_e/M)` cap with surplus). Changing the heavy state at `P` in one color changes that color's optimum capped recourse by at most

`B_P=sum_(e incident P)q_e C_e=(12/N)a_P`.

To see this, delete every edge incident to `P` from an optimal flow in either state; the remaining flow is feasible in both states and the deleted profit is at most `B_P`. Now independently assign each heavy pair's edges to colors by a uniformly random injection. A transposition of two color slots in pair `P` changes the palette support sum `H_q=sum_c F_q(R^c,C)` by at most `2B_P`. Exposing each pair's random permutation slot by slot and coupling alternative revealed values by a transposition gives martingale differences `O(B_P)`. Azuma's inequality and `M=Theta(N)` yield, for a universal constant `c>0`,

`Pr[H_q <= E H_q-t] <= exp[-c t^2/(M sum_P B_P^2)] <= exp[-c' t^2 N/(sum_P a_P^2)]`.

In particular, every **fixed** normalized `q` has `O(N^(-1/2))` fluctuations uniformly in graph order; spread-out profits concentrate faster. This bypasses the nonlocality of the conditional flow policy because it bounds the optimal value itself by deleting pair-incident flow. It does **not** imply that one heavy injection satisfies the continuum of profit inequalities simultaneously. A direct union bound over all edge-supported `q` would reintroduce graph order, and the pure-schedule counterexample above shows that a positive expectation alone is insufficient. A graph-order-independent maximal inequality or local-lemma reduction over dual directions is the remaining concentration target.

The existing manuscript `thm:round` handles simple support with per-edge/color fractions `O(1/N)` and local knapsack hull, while `lem:bp-mult-round` permits only fixed pair multiplicity. The minimal cap supplies the small-fraction condition for tiny edges; the heavy matching pairs can still have `Theta(N)` parallel physical edges, and the deterministic finite table is missing. Applying those lemmas as written would silently assume away the two remaining conditions.
