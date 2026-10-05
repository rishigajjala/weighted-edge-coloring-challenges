# Path gate for a folded guard pair on a fluid tree

4 October 2026. Exact structural lemma toward a general paired-activation transfer. No global `2/3` bound is claimed.

Let `T` be a tree of divisible-fluid edges with nonnegative profits and fixed edge caps, and let distinct vertices `u,v` be the two ports of one unit-heavy guard pair. Hold the active/busy states of every other vertex fixed. Write `f_ij` for the optimal capped fluid recourse on `T` when `u` has active bit `i` and `v` has active bit `j`.

**Path-gate identity.** If any internal vertex of the unique `u`–`v` path in `T` is busy, then

`f_11+f_00-f_10-f_01=0`.

Indeed that busy vertex deletes every path joining `u` to `v`, so the remaining active fluid graph splits into components, with `u` and `v` in different components. Recourse is the sum of the independent capped optima over those components. Hence changing `u` has the same effect regardless of `v`, making the cross difference zero. The argument allows branches, heterogeneous profits, and parallel physical fluid identities along any tree adjacency (parallel identities simply share the same two endpoints).

If the pair's free marginal is `p` and is independent of all other source pairs, replacing independent free bits at `u,v` by their common pair bit changes conditional recourse by exactly `p(1-p)` times this cross difference. Therefore its entire correlation effect is supported on the event that **every internal path vertex is active**. For a bipartite tree, opposite-shore endpoints have nonnegative cross difference and require no repair; same-shore endpoints have nonpositive cross difference. In the latter case, monotonicity also bounds its magnitude by the smaller of the two singleton gains `f_10-f_00` and `f_01-f_00`.

This identifies the two-spoke guarded star as the shortest adverse path: its paired leaves lie at distance two and only the center must be active. A longer even path inserts more required active vertices. That observation alone is not a theorem: internal free probabilities can approach one, and two internal vertices may be correlated through another guard pair. A quantitative forest proof would need to charge these path-gated losses against the boosted independent-vertex surplus and the hybrid common-threshold gain, while avoiding double counting when many folded pairs have overlapping paths.

## Quantitative bottleneck on any tree path

For any adjacency `e` on the `u`–`v` path, delete **all** its parallel fluid identities. Let `F^0_ij` be recourse after deletion. It is additive between the two sides of this cut, so its four-state cross difference is zero. In each state the gain `G_ij=f_ij-F^0_ij` is between zero and `W_e:=sum_{a parallel to e} q_a C_a`: deleting every cut-edge flow from a full optimum leaves a feasible no-cut flow and sacrifices at most `W_e`. Consequently

`|f_11+f_00-f_10-f_01| = |G_11+G_00-G_10-G_01| <= 2 W_e`.

Minimize over edges of the path. Combined with the path gate, this gives the conditional same-shore pairing loss at most

`2 p(1-p) * 1_{all internal path vertices active} * min_{e on path} W_e`.

Upon averaging the other source states, multiply the right side by the probability that all internal path vertices are active. This estimate works with arbitrary nonnegative profits and fixed caps, without assuming any independence among those internal vertices. It is too coarse by itself to prove the `2/3` transfer: `C_a=12y_a` leaves a factor 24 in the cut charge, and many folded-pair paths may share one cut. It does show that a long-range paired interaction must pass through an active, profit-capacitated path and cannot have size independent of a small bottleneck bundle.
