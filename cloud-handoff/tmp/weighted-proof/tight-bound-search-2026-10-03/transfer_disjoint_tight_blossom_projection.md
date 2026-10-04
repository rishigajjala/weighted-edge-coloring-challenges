# Disjoint tight-blossom projection for arbitrary heavy weights above 1/2

**Status: proved reduction, independently audited by the parent agent; blossom repair remains open.** This applies to arbitrary loopless heavy and divisible-fluid multigraph supports, with every heavy weight `w_e>1/2`. It does not prove the unrestricted mixed-model `3/2` inclusion. The near-unit `w_e>=4/5` repair is proved separately in `transfer_near_unit_exact_three_halves_blossom_repair.md`.

Fix any locally feasible `(x,y)` and set `alpha=2/3`. Regard heavy and fluid types as auxiliary unit edges, and write `z=(alpha x,alpha y)`. If `w_min` is the minimum heavy weight (put `w_min=1` when there are no heavy types), then at every vertex

`deg_v z =alpha(h_v+d_v) <=alpha[1+(1-w_min)h_v] <=alpha(2-w_min)<1`.

The heavy-only subvector `z^H=(alpha x,0)` belongs to the ordinary matching polytope: its degrees are at most `alpha`, and for any odd set `S` with `|S|>=3`,

`z^H(E(S))<=alpha |S|/2=|S|/3<=(|S|-1)/2`.

Consequently the nonempty compact set

`P={z' in ordinary matching polytope : z'_e=z_e for heavy e, 0<=z'_f<=z_f for fluid f}`

has a maximizer of `sum_f z'_f`. Fix one. Every vertex-degree inequality is **strict** at `z'`, because `z'<=z` coordinatewise. If a fluid coordinate `f=uv` was reduced, `z'_f<z_f`, then some odd-set inequality containing both `u,v` must be tight at `z'`: otherwise a sufficiently small increase of this coordinate preserves all finitely many matching-polytope inequalities and improves the objective. (The nonnegativity lower bound cannot stop an increase.)

Call an odd set `S` tight when `z'(E(S))=(|S|-1)/2`. Any two distinct **inclusion-maximal tight odd sets are vertex-disjoint**. Here is the complete uncrossing argument. Suppose tight odd `S,T` overlap, and write `I=S intersection T`, `U=S union T`.

* If `|I|` is odd, then `|U|` is odd. Nonnegativity gives

  `z'(E(S))+z'(E(T)) <= z'(E(I))+z'(E(U))`.

  The two sides have the same blossom right-hand-side sum, since `|S|+|T|=|I|+|U|`. Feasibility forces equality, so `U` is tight. Thus distinct incomparable tight `S,T` cannot both be inclusion-maximal.

* If `|I|` is even, then `A=S\T` and `B=T\S` are odd. Counting edges by regions gives

  `z'(E(S))+z'(E(T)) <= z'(E(A))+z'(E(B))+sum_{v in I}deg_v z'`.

  The odd-set bounds for `A,B`, together with tightness of `S,T`, force `sum_{v in I}deg_v z'>=|I|`. But every degree is strictly below one, a contradiction.

Thus maximal tight odd sets form a pairwise vertex-disjoint family. Every reduced fluid type has both endpoints in one of these maximal blossoms. In every ordinary matching `M` in any decomposition of `z'`, a maximal tight blossom `S` of size `2k+1` has exactly `k` internal selected edges: its expected internal count equals `k`, while no matching can exceed `k`. Hence each such state leaves exactly one vertex of `S` unmatched by internal edges; that vertex may carry a crossing matching edge.

This isolates the missing step. One must restore the removed fluid types **inside each disjoint maximal tight blossom**, retaining the fixed heavy-edge marginals, while respecting possible crossing unit edges and the nested tight odd subsets within a maximal blossom. The triangle proof handles the special case in which all maximal blossoms have size three and are disjoint. No arbitrary-size repair lemma is established here.
