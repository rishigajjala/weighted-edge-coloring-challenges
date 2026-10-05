# Pair-correlation loss: exact identity and a componentwise safe regime

4 October 2026. This is a scoped structural checkpoint for the `2/3` capped unit-guard problem, not a proof for arbitrary fluid support.

Let `F_q(A,C)` be optimum divisible-fluid recourse when binary active vertex set is `A`, with fixed edge caps. Conditional on every other activation, write `f_ij` for recourse when the two endpoints of one heavy pair are respectively in states `i,j`. If each endpoint is independently free with probability `p`, then replacing them by one common free bit with the same marginal changes expected recourse by exactly

`p(1-p) [f_11+f_00-f_10-f_01]`.

When these vertices lie on the same shore of a bipartite fluid component, the bracket is nonpositive by the capped matching exchange lemma; when they lie on opposite shores, it is nonnegative. In the same-shore case, monotonicity gives the elementary bound

`0 <= f_10+f_01-f_11-f_00 <= min(f_10-f_00, f_01-f_00)`.

This is an exact local correlation-loss certificate, but it cannot be charged by a tiny universal fraction of the target profit. Let the pair be the two leaves of a unit-profit two-spoke star, with center always free and both leaf free probabilities `p=1/2`. Then `f_00=0`, `f_10=f_01=f_11=1`: the correlation loss is `1/4`, while the natural local target with leaf allowances `D=1/4` has total profit `1/2`. Thus the loss can be half the target value. The center availability and local degree constraints supply additional slack; a simple additive loss estimate alone does not explain the hybrid law.

There is nevertheless a broad safe regime. Suppose the fluid graph may be nonbipartite and have arbitrary profits and parallel edges, but **each connected component contains at most one endpoint of every unit-heavy guard pair**. Under independent pair activation at heavy marginals `2x/3`, activations of vertices *within each fluid component* are mutually independent: each component observes at most one bit from each pair source. Dependencies between different components are irrelevant because recourse is additive over components. A vertex with local residual allowance `D_v` is free with `p_v=1/3+2D_v/3`, which is at least `1/4+3D_v/4`. The capped independent-vertex `3/4` theorem, valid on arbitrary fluid graphs by the bipartite double-cover argument, therefore gives componentwise

`E F_q(A,C) >= (3/4) q·y >= (2/3)q·y`

for every target `y` satisfying the local degree rows and `C_e>=12y_e`. Thus no intercomponent guard dependence needs repair. An independent-law obstruction requires at least one guard pair whose two endpoints occur in the same fluid component; the exact two-spoke obstruction has precisely that feature.

The componentwise result is stronger than merely deleting guard pairs whose endpoints lie in different fluid components: it permits arbitrarily many other guard pairs and arbitrary internal fluid topology, including odd cycles. It does not handle an internally folded pair, where its two ports can be substitutes for the same fluid resource. The hybrid common-uniform mode supplies favorable correlations between different guard pairs in the proved star and bridge cases, but the displayed single-pair identity alone does not control its effect on an arbitrary connected component.
