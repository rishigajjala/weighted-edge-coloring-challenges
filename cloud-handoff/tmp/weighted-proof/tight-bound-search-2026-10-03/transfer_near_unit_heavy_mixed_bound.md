# A uniform near-unit heavy bound with arbitrary fluid support

**Status: proved.** Let the discrete types have weights in
`[1-epsilon,1]`, where `0<=epsilon<1/2`; their support, parallel types,
and nonnegative profits are arbitrary. Let all other edges be
arbitrarily divisible fluid with arbitrary support and densities.
The full local configuration hull `P` and global mixed-pattern hull
`Q` satisfy

`[2/(3(1+epsilon))] P subset Q`.                    (1)

Thus the mixed configuration gap is at most
`(3/2)(1+epsilon)` uniformly in graph size and type count. At
`epsilon=0` this recovers the exact unit-heavy theorem. In
particular, a sequence of counterexamples with a gap bounded above
`3/2` by a fixed positive amount cannot have all discrete weights
tending to one.

**Proof.** At one vertex `v`, every feasible local pattern contains
at most one discrete heavy item. Let `x_e` be its mean integer count
on each discrete type and `y_f` its mean fluid amount. Local
feasibility gives

`sum_{e incident v,heavy} x_e<=1`,
`sum_{e incident v,heavy} w_e x_e + sum_{f incident v,fluid} y_f<=1`.

Since `1-w_e<=epsilon`, their sum implies

`sum_{e incident v,heavy} x_e + sum_{f incident v,fluid} y_f`
`<=1+epsilon sum_{e incident v,heavy}x_e<=1+epsilon`. (2)

Treat each discrete type and fluid edge as an ordinary unit edge.
Equation (2) says `z=(x,y)/(1+epsilon)` lies in the
degree-constrained fractional matching polytope of this multigraph.
For every odd vertex set `S` of size at least three, degree
constraints give `z(E[S])<=|S|/2`. Hence

`(2/3) z(E[S])<=|S|/3<=(|S|-1)/2`.

All degree and nonnegativity inequalities also hold after scaling.
The ordinary matching-polytope theorem therefore places `(2/3)z`
in the convex hull of matchings. A selected discrete edge is an
actual feasible one-item packet because `w_e<=1`. A selected fluid
edge may carry one unit of fluid. The selected edges form a
matching, so every such outcome is a globally feasible mixed
pattern. Their mean vector is exactly the left side of (1). `□`

This argument uses only ordinary matching patterns. Its
`1+epsilon` loss comes from replacing a selected weight
`1-epsilon` discrete packet by a unit-occupied matching edge;
recovering the exact `3/2` coefficient for arbitrary weights in
`(1/2,1]` requires using those residual capacities rather than
discarding them.
