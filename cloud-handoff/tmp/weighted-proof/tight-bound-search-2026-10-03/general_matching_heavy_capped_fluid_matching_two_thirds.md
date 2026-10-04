# Capped 2/3 transfer when the fluid simple support is a matching

4 October 2026. This scoped one-color theorem works without an explicit bipartiteness assumption, but **the union of the two simple matchings is automatically bipartite**: every cycle alternates heavy and fluid edges and is even. Thus it is not a genuinely nonbipartite advance. It is not an integer physical palette theorem and does not cover fluid edges sharing vertices.

Heavy types have weights in `[0,1]` and categorical groups on simple pairs whose support is a matching, so the full local heavy marginals `x_h` admit a feasible heavy-matching law (sample each disjoint group categorically). The divisible fluid simple support is also a matching, although parallel fluid types on one simple pair are allowed. Let `y_e` be locally feasible fluid targets under the mean heavy loads, and give each fluid type a per-color cap `C_e>=2y_e`. Then a one-color distribution has heavy marginals `2x_h/3` and exact fluid means `2y_e/3`.

Take any full-heavy-marginal law and mix it with the empty-heavy state with probabilities `2/3,1/3`. Fix a fluid simple pair `uv`, write `Y=Σ_{e on uv}y_e`, and let `R_u,R_v∈[0,1]` be its residual capacities under the full law. Local feasibility gives `E R_u,E R_v>=Y`. Different fluid simple pairs have disjoint vertices and can be routed independently in every state.

If `Y<=1/2`, route `2y_e` on every parallel fluid type in the empty-heavy state and zero in the full-heavy state. Its total is `2Y<=1`, it respects `C_e>=2y_e`, and its mean is exactly `2y_e/3`.

If `Y>1/2`, put `T=min(R_u,R_v)` in a full-heavy state and `T=1` in the empty state; route `T y_e/Y` on each parallel type. The total is at most each endpoint's residual. Since `T<=1` and `1/Y<2`, each type's amount is at most `y_e/Y<2y_e<=C_e`. Pointwise `min(R_u,R_v)>=R_u+R_v−1`, so `E_full T>=2Y−1`. The mixture's expected total route is at least

`(2/3)(2Y−1)+(1/3)=(4Y−1)/3 >= 2Y/3`,

where the final inequality uses `Y>=1/2`. Thus every parallel type receives mean at least `2y_e/3`; thin the total route on this pair by a fixed factor to make all its type means exact. Perform this independently on every disjoint fluid pair. Heavy marginals remain exactly `2x_h/3`.

The proof does not use independence among heavy groups: any full-marginal heavy law works. It also shows why a common empty-heavy coin suffices for fluid matching support but fails for diffuse capped stars: the empty state's unit capacity is spent at each pair separately here, while a star's edges compete at one center (`general_matching_heavy_capped_global_coin_obstruction.md`).

More generally, on *any* fluid support, if the local fluid load at every vertex is at most `1/2`, the same global empty coin routes `2y_e` on **all** fluid edges in its empty state and routes zero in full-heavy states. The cap premise `C_e>=2y_e` and vertex load premise make this feasible. The hard capped regime therefore requires vertices with fluid target load greater than `1/2`; a diffuse star has exactly such a center.
