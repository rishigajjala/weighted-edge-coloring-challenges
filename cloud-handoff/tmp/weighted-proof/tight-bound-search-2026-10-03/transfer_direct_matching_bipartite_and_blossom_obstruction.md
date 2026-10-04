# Direct unit-matching rounding for bipartite heavy-plus-fluid support

**Status.** The bipartite mixed-model theorem below is proved, with arbitrary heavy support and arbitrary divisible-fluid support. The general-graph blossom repair remains open. This does not transfer by itself to arbitrary finite tiny-edge stocks in the original coloring problem.

Let the heavy edge types have weights `w_e>1/2` and local means `x_e`. Let fluid edge amounts have local means `y_f`. At every vertex `v`, the exact local hull imposes

`h_v=sum_{heavy e incident v}x_e<=1`,

`sum_{heavy e incident v}w_e x_e+d_v<=1`, where `d_v=sum_{fluid f incident v}y_f`.

Set `alpha=2/3` and treat both heavy and fluid types as **unit edges** in an auxiliary multigraph. Its fractional edge vector is `z=(alpha x,alpha y)`. At each vertex,

`deg_v z=alpha(h_v+d_v) <= alpha[1+sum_{heavy e incident v}(1-w_e)x_e] <= alpha(1+h_v/2)<=1`.

The strict sign can be replaced by `<=` when allowing weight `1/2`; the result still holds under the stated strict condition. If the combined heavy-plus-fluid support is bipartite, the ordinary bipartite matching polytope is described by nonnegativity and vertex-degree inequalities. Therefore `z` is a convex combination of ordinary matchings, with exact coordinatewise marginals `alpha x_e,alpha y_f`. In each such matching, realize a heavy edge as one weight-`w_e` item and a fluid edge as one unit of divisible fluid. Edges are vertex-disjoint, so this is a physically feasible mixed pattern. Thus the entire scaled local hull lies in the physical global hull, proving a `3/2` configuration bound for this unrestricted-support **bipartite mixed model**.

For a general combined support, the same `z` is in the ordinary *degree* polytope. If it also satisfies every ordinary odd-set inequality

`sum_{g inside S}z_g <= (|S|-1)/2` for odd `S`,

the same direct decomposition proves physical inclusion. Consequently every point requiring a new argument violates at least one odd-set inequality of the auxiliary unit matching polytope.

There is a quantitative necessary condition for such a violation. Let `|S|=2k+1`, let `R_v=sum_{heavy e incident v}(1-w_e)x_e`, and let `c_S` be the total *unscaled* heavy-plus-fluid mass of edges with exactly one endpoint in `S`. Summing the local degree bounds over `S` gives

`2 sum_{g inside S}(x_g+y_g)+c_S <= |S|+sum_{v in S}R_v`.

After scaling by `2/3`, its ordinary blossom excess `delta_S=sum_{g inside S}z_g-k` obeys

`delta_S <= [sum_{v in S}R_v-c_S-(k-1)]/3`.

Thus a violated `S` requires `sum_{v in S}R_v>k-1+c_S`. In particular, when all heavy weights are at least `4/5`, every odd set of size at least five satisfies its ordinary matching inequality: for `k>=2`, `sum_{v in S}R_v <= (2k+1)/5 <= k-1` (equality only at `k=2`). Only triangles can then violate the unit-matching polytope. This is a structural observation, **not** a blossom repair or a proof of the general `3/2` theorem.

More generally, if every heavy weight is at least `1/2+epsilon` for a fixed `epsilon>0`, then `R_v<=(1/2-epsilon)h_v<=1/2-epsilon`. The preceding necessary condition shows that every violated odd set has `|S| epsilon <3/2`. Thus only odd blossoms of bounded cardinality `|S|<3/(2epsilon)` can obstruct the direct unit-matching decomposition. This bound concerns *ordinary* matching blossoms; it does not give a repair or a finite-stock coloring theorem.

The direct scalar support formulation of the remaining problem is

`max_{heavy matching A} [p(A)+F_q(1-W1_A)] >= (2/3) max_{local (x,y)}[p·x+q·y]`,

where `F_q(r)=max{q·u:u>=0, deg u<=r}` and `p,q>=0`. It is equivalent to the desired general mixed-model inclusion by downclosed convex separation. A local LP minimax identity is

`max_{local (x,y)}[p·x+q·y] = min_{b>=0: b_u+b_v>=q_f} [sum_v b_v+FM(p_e-w_e(b_u+b_v))]`,

where `FM` is maximum weight **degree-relaxed fractional matching** on heavy edges, with negative edge coefficients optimally assigned zero. The physical objective has the reverse-order form

`max_{heavy matching A} min_{b>=0: b_u+b_v>=q_f}[sum_v b_v+sum_{e in A}(p_e-w_e(b_u+b_v))]`.

Ordinary matching rounding bounds `FM` for each fixed `b`, but does not justify exchanging the outer maximum over `A` and the minimization over `b`. A valid general proof must account jointly for blossom violations and this minimax loss. No such argument or counterexample was obtained here.
