# A 3/2 bound for asymmetric triangle-factor networks with divisible spokes

This is a theorem for the specified divisible-fluid model, not for
arbitrary weighted multigraphs. It rules out compounding a triangle's
internal `3/2` gap with frustrated blocker correlations in this family.

Take a matching of blocker edges, with arbitrary individual weights in
`[1/2,1]`. After deleting them, suppose every nontrivial factor
is a vertex-disjoint triangle with two blocker ports `a,b` and a private
hub `c`. The edge `ab` is a unit direct edge with arbitrary nonnegative
profit `q`; the spokes `ac,bc` are divisible fluid with arbitrary
nonnegative per-unit profits `u,v`. Each port is incident with at most
one blocker, and the two ports of a factor are incident with **distinct**
blockers. A blocker may connect ports in distinct factors, so the
factor-blocker incidence can be a cycle, a branch, or more generally
any matching-linked network. Blocker profits are arbitrary nonnegative.

**Claim.** The maximum profit of a globally feasible one-color pattern
is at least `2/3` of the maximum profit in the ordinary vertex-local
configuration relaxation.

Let `x,z` be the local means of the two blockers touching a factor,
whose weights are `h_a,h_b in [1/2,1]`.
Write `p,l,r` for the direct-edge and spoke means. The exact local
constraints at these three vertices are

    0<=p<=1-max(x,z),
    0<=l<=1-h_a*x-p,  0<=r<=1-h_b*z-p,  l+r<=1.      (1)

The two inequalities behind the bound on `p` are needed because a
unit direct edge cannot coexist with either blocker, even when
their sum of average weights is at most one. Conversely (1) describes
the projection of the three vertex-local pattern hulls exactly.

Independently activate every blocker `i` with probability
`(2/3)x_i`. Conditional on these choices, optimize each factor's
direct/spoke edges. Their vertex sets are disjoint, and a selected
blocker only reduces its two endpoint residual capacities, so the
conditional factor optima and all selected blockers combine into a
feasible global color. Each blocker's expected profit is exactly
`2/3` of its local profit. It remains to prove the following single
factor inequality for every `x,z,h_a,h_b,q,u,v`:

    E[best factor profit | independently activated blockers]
      >= (2/3) max_{(p,l,r) satisfying (1)}(q*p+u*l+v*r). (2)

By exchanging ports assume `u>=v`. On each of the two cones `q>=u>=v`
and `u>=v, u>=q`, every conditional optimal profit is linear in
`(q,u,v)`, whereas the right side of (2) is convex and positively
homogeneous. It therefore suffices to verify the five generating
profit rays

    (q,u,v) = (1,0,0), (0,1,0), (1,1,0),
              (0,1,1), (1,1,1).                         (3)

Put `T=h_a*x+h_b*z`, `delta=h_a+h_b-1`, and let `E` denote the left side
of (2). For the direct-only
ray, the local optimum is `1-max(x,z)` and

    E=(1-2*x/3)(1-2*z/3)
      >= (1-2*m/3)^2 >= (2/3)(1-m),  m=max(x,z).

The last difference is `(4*m^2-6*m+3)/9>0`.

For both the left-spoke-only ray and the direct-plus-left-spoke ray,
the local optimum is `1-h_a*x`: the direct edge is dominated by the
left spoke with equal profit. In both cases `E=1-2*h_a*x/3`, which
exceeds `(2/3)(1-h_a*x)` by `1/3`.

For the remaining two rays, every conditional factor profit has the
same value: it is `1` unless both blockers are selected, when it is
`2-h_a-h_b=1-delta`. Therefore in both cases

    E=1-delta*4*x*z/9.                                (4)

Because `x,z<=1` and `delta<=1`,

    T >= (h_a+h_b)*x*z = (1+delta)*x*z >= 2*delta*x*z,

so (4) implies `E >= 1-2*T/9`.

For the two-spokes ray, the local optimum is
`g=min(1,2-T)`. If `T<=1`, then (4) gives

    E >= 1-2*T/9 >= 7/9 > (2/3)*g.

If `T>=1`, then `g=2-T`; using the bound after (4),

    E-(2/3)*g >= -1/3 + 4*T/9 >= 1/9.

For the all-three ray, fixing `p` leaves maximum spoke profit
`min(1,2-T-2*p)`, so the local optimum is

    g=max_{0<=p<=1-max(x,z)}
          [p+min(1,2-T-2*p)]
      <= 3/2-T/2.                                     (5)

The bound (5) follows by observing that either `p<= (1-T)/2`,
when the expression is at most `1+p`, or `p>= (1-T)/2`, when it is
at most `2-T-p`. Their minimum is at most their common value
`3/2-T/2`; the conclusion also holds if the crossing is outside
the feasible interval. The bound after (4) implies

    E >= 1-2*T/9 >= 1-T/3 >= (2/3)*g.

Thus (2) holds on all five rays and hence on all nonnegative profit
vectors. Summing across factors proves the claim.

The factor `3/2` is attained already with no blockers: for
`q=u=v=1`, the triangle's local means `p=l=r=1/2` have profit `3/2`,
while one global factor color earns at most `1`. The proof relies on
divisible spokes and a unit direct edge. It makes no assertion for
discrete medium/spoke types or factors incident with three or more
blockers; those are concrete directions for a stronger lower bound.
