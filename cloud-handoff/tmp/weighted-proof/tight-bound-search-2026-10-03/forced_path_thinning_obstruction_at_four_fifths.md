# A scaled-law obstruction beyond full-law thinning

**Interim scope.** This is an exact negative result about one proposed proof method for the bipartite categorical-heavy plus uncapped-fluid mixed hull. It does not refute the `4/5` hull inclusion; the same instance has a feasible scaled law.

Use the four-heavy-edge path and one fluid edge from `bipartite_mixed_fluid_sharpness_audit.md`: path vertices `v_R--a_L--b_R--u_L--c_R`, heavy edges `e_1,...,e_4` in path order, weights `(1,1,1/2,1)`, and full marginals `(2/3,1/3,2/3,1/3)`. The fluid edge is `uv` with local target `y=1/3`. Every full-marginal heavy law is forced to use `M_0={e_1,e_3}` with probability `2/3` and `M_1={e_2,e_4}` with probability `1/3`; fluid recourse is zero in both full states.

Suppose a scaled heavy law is constructed by first sampling this forced full matching `M`, and then deleting selected edges, without ever adding an edge outside `M`. Require the correct scaled heavy marginals `alpha x` with `alpha=4/5`. Each heavy edge appears in only one of the two full states, so every selected edge must have conditional retention probability exactly `4/5` in its own full state.

In state `M_0`, fluid endpoint `v` is blocked by the unit-weight `e_1`; positive fluid recourse requires deleting `e_1`, an event of conditional probability `1/5`. Even when that happens, fluid recourse is at most one. In state `M_1`, endpoint `u` is blocked by unit-weight `e_4`; positive recourse requires deleting `e_4`, also conditional probability `1/5`. Therefore every such per-state thinning law, with arbitrary correlations among deletions, has

`E F_{uv}(M_new) <= (2/3)(1/5)+(1/3)(1/5)=1/5`.

The desired fluid marginal at scale `4/5` is `(4/5)(1/3)=4/15>1/5`. Hence no proof based on thinning each sampled full matching separately can establish `4/5` for this one-fluid-edge instance. In particular, assigning selected edges to five deletion phases cannot work, even with arbitrary phase collisions. A successful scaled law must transport probability mass *between* the two full matching states and partial matching states. The exact optimized scaled law in the sharpness audit achieves recourse `3(1−alpha)/2=3/10` at `alpha=4/5`, exceeding the required `4/15`.

The same calculation persists for strict-heavy weights `w_{e_3}=1/2+epsilon` with adjusted feasible fluid target tending to `1/3`; the limiting separation between `1/5` and `4/15` is positive.

## The cross-state exchange that repairs this instance

At `alpha=4/5`, the standard full-plus-empty law has masses `8/15` on `M_0`, `4/15` on `M_1`, and `1/5` on the empty matching. Remove mass `1/5` from each of these three states, and replace it with mass `1/5` on each of

`{e_3}`, `{e_2}`, `{e_1,e_4}`.

This preserves every edge marginal: across the three removed states each of `e_1,e_2,e_3,e_4` occurs exactly once, and the same is true across the three inserted states. The remaining masses are `1/3` on `M_0` and `1/15` on `M_1`; all masses sum to one. The three inserted states have fluid recourse `1/2`, `1`, and `0`, respectively, so the repaired law has expected recourse `(1/5)(3/2)=3/10`, matching the exact optimum from the sharpness audit.

This is a `3`-state edge-coloring exchange: take one copy of each of two heavy matchings and one empty matching, then repartition their union into three different matchings. It transports mass between the full states before scaling. For arbitrary two matchings, a proper three-edge-coloring of their union always preserves the edge incidence multiset and hence all marginals, but no general recourse-improvement guarantee has been proved. The forced path shows why such cross-state moves are relevant to a `4/5` transfer with heterogeneous saturated heavy vertices.
