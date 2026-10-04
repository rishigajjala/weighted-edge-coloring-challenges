# Capped three-quarters transfer through bipartite dependent rounding

3 October 2026, audited again on 4 October. Two independent agents checked
the exchange proof, curvature signs, rounding law, and separation step;
no gap was found at the stated scope. The separate audit is
`common_weight_capped_pipage_independent_audit.md`. This
is a one-color fractional statement, not an unrestricted physical-edge
coloring bound or a finite-palette theorem. The heavy support may be any
bipartite multigraph, provided each connected heavy component has one
common edge weight. Different components may have different weights.

## Statement

The combined heavy and fluid graph is bipartite. Heavy marginals x obey
sum_{h at v} x_h <= 1. Heavy weights w_h are in [0,1] and are constant on
each connected heavy component. Fluid targets y obey

    sum_{e at v} y_e <= D_v := 1 - sum_{h at v} w_h x_h.

Every fluid edge has a cap C_e >= 12 y_e. Then the candidate conclusion
is a law of heavy matchings and feasible capped fluid flows with means
(3x/4, 3y/4). A selected heavy edge consumes its actual weight at both
endpoints. Fluid respects all residual vertex capacities and its caps.
The categorical restriction that selected heavy edges form a matching is
imposed even if a heavy weight is below 1/2.

The heavy matching law below does not depend on fluid profits or caps.

## Signed exchange inequalities for capped bipartite flow

For nonnegative fluid profits q and a fixed fluid cap vector C, write
f(S) for maximum profit with capacity one on vertices in S and zero on
the others. Then for u,v outside S:

* if u,v are on the same shore,
  f(S+u)+f(S+v) >= f(S+u+v)+f(S);
* if they are on opposite shores, the inequality is reversed.

Here is a flow-exchange proof of the first inequality. Take optimal red
flow for S+u+v and blue flow for S, and retain their common edgewise
minimum. Orient remaining red excess left-to-right and blue excess
right-to-left. Suppose u,v are on the left (the right case is symmetric).
They are pure sources in this directed difference flow. Decompose it
into source-to-sink paths and directed cycles. Swap red and blue along
all path portions originating at v. No such path passes through u,
which has no incoming excess. The two resulting flows use S+u and S+v,
respectively. Intermediate vertex loads are unchanged; at each terminal
the new loads lie between the old red and blue loads. Each edge's two
new amounts lie between its old two amounts, so both obey C. Total profit
of the two flows is preserved. This gives the inequality. The usual
opposite-shore exchange, starting from the two one-added states, proves
the reverse inequality (see five_hour_capped_activation_audit.md).

Let Phi(p)=E f(A), where vertices enter A independently with probabilities
p_v. Its mixed derivative in p_u,p_v is the expected four-state cross
difference. It is therefore nonpositive for same-shore pairs and
nonnegative for opposite-shore pairs. Phi is affine in each coordinate.

## Round the heavy vector without decreasing Phi

Put alpha=3/4 and begin at z=alpha x in the bipartite matching polytope.
For a vertex incident to the heavy component of common weight w, put
p_v(z)=1-w sum_{h at v} z_h; a heavy-free vertex has p_v=1.
Initially p_v=1/4+3D_v/4.

Perform the standard alternating-path/cycle dependent rounding of z.
In the graph of fractional heavy edges, choose an even cycle if one
exists; otherwise choose a maximal path. Add a scalar t to alternate
edges and subtract it from the other edges. Choose the two endpoints
of the maximal feasible t interval with probabilities preserving E t=0.
At least one fractional edge becomes integral. Iterate to an integral
matching M; every physical heavy identity has inclusion probability
alpha x_h.

On a cycle every heavy degree, hence every p_v, is constant. On a path,
only its two endpoint degrees change. If its endpoints are on the same
shore, their changes have opposite signs; if on opposite shores, the
changes have the same sign. The path lies in one common-weight heavy
component. Thus the second derivative of Phi(p(z(t))) is a nonnegative
multiple of minus the same-shore cross derivative, or a nonnegative
multiple of the opposite-shore cross derivative, respectively. In
both cases Phi is convex along the rounding interval. Conditional
Jensen at every step yields

    E_M Phi(R(M)) >= Phi(1/4+3D/4),

where R_v(M)=1-w if v is heavy-covered and one otherwise.

The rounding choices may be fixed by graph structure and current z;
none needs q. The same resulting heavy law satisfies this inequality
for every q>=0 and every fluid cap vector C.

## Recover actual residual capacities and target means

Let F_q(r,C) be capped fluid recourse with real vertex capacities r.
It is jointly concave in r: convex combinations of feasible flows give
the corresponding convex combination of capacities and profits.
For each fixed heavy matching, independent Bernoulli capacities of
means R therefore give

    F_q(R,C) >= Phi(R).

The already audited capped independent-activation lemma, with caps
C>=12y, gives Phi(1/4+3D/4) >= (3/4) q.y. Hence

    E_M F_q(R(M),C) >= (3/4) q.y.

For the fixed heavy matching law, the set of attainable mean fluid
vectors is compact, convex, and downward closed. Its support value in
direction q is E_M F_q(R(M),C). Separation in nonnegative directions
therefore puts (3/4)y in that set. This supplies all fluid coordinate
means simultaneously, while preserving heavy means (3/4)x.

## Exact remaining limits

Heterogeneous heavy weights invalidate the endpoint-only change in p:
an alternating perturbation can change weighted load at every internal
path vertex. The signed two-coordinate curvature argument then gives
no conclusion. This is a limitation of this proof, not a counterexample
to the desired inclusion.

The law can also have global state dependence along long alternating
paths. The finite-label bridge for independent heavy pairs cannot be
invoked merely from this fractional inclusion. A local realization or
a new exact-stock palette transfer is still needed for physical edges.

The modular bridge in `bounded_heavy_component_transfer_interface.md`
handles the case where every heavy component has a fixed bounded number
of vertices; its palette overhead can depend on that bound. It does not
handle unbounded components.

An exact failure of the same generic rounding rule with heterogeneous
weights is recorded in `heterogeneous_pipage_chord_exact_obstruction.md`.
That example needs extra correlation during later rounding; it is not
a counterexample to the mixed-hull inclusion.

Related primary source: Saha and Srinivasan, A New Approximation Technique
for Resource-Allocation Problems, Theorem 4.4 and its appendix discuss
same-shore coverage negative correlation under bipartite dependent
rounding, https://www.cs.umd.edu/~srin/PDF/2018/2018-RSA-jou.pdf.
The present argument uses the explicit signed exchange inequalities
above; same-shore negative correlation by itself is insufficient.
