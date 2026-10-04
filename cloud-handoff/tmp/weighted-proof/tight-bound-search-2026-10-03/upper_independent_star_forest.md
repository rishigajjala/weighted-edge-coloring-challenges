# Independent-capacity star forests: an exact `1+1/e` fluid configuration bound

**Status:** Proved below for the divisible-fluid mixed model. This is not an
integer weighted-edge-colouring theorem. It permits arbitrarily many fluid
star components and cycles in the graph linking them through discrete pairs.

## Model and theorem

Let the discrete support be a matching of vertex pairs. A pair `i` may
carry an arbitrary finite collection of integer packet types; a sampled
feasible packet has load `W_i in [0,1]` at *both* endpoints and leaves
residual `R_i=1-W_i`. Different pairs have prescribed arbitrary packet
laws. Other vertices have residual one. The remaining edges are
arbitrarily divisible fluid edges of nonnegative profit densities `q_e`.

Suppose the fluid support is a vertex-disjoint union of stars (an isolated
edge is a star), and **each discrete pair meets each fluid-star component
in at most one vertex**. The same pair may meet two different components,
and the resulting pair/component incidence graph may have cycles.

For the full local configuration polytope `P` and global mixed-pattern
polytope `Q`, where fluid amounts are divisible and discrete packets remain
integer, the exact support-function inequality is

`max_{x in P} p.x <= (1+1/e) max_{z in Q} p.z`              (1)

for every nonnegative additive profit vector `p` on discrete types and
fluid edges. Equivalently, `(e/(e+1))P subset Q`, using downward closure.
No bound on the number of stars, packets, weight types, or minimum positive
discrete weight is needed.

## Independent-capacity star lemma

Let one fluid star have independent capacities `X,R_1,...,R_m in [0,1]`
at its hub and leaves, respectively; fixed-capacity vertices correspond to
constant one. Put `x=E X`, `r_i=E R_i`, and `A=max_i q_i` (`A=0` for an
empty star). If `F_q` is maximum feasible fluid profit, then

`E F_q(X,R) >= F_q(x,r)-A/e`.                         (2)

Order edges by decreasing density. The fractional-knapsack layer-cake
identity is

`F_q(X,R)=integral_0^A min(X, sum_{i:q_i>=t} R_i) dt`.  (3)

At any threshold, write `S=sum R_i` over active leaves, `mu=E S`, and
`x=E X`. The elementary pointwise inequality

`min(1,S) >= 1-product_i(1-R_i)`

follows by interpreting each `R_i` as a conditional independent event
probability and applying the union bound. Independence gives

`E min(1,S) >= 1-product_i(1-r_i) >= 1-exp(-mu)`.    (4)

Also `min(X,S)>=X min(1,S)` pointwise. Since the hub capacity is
independent of all leaf capacities, (4) yields

`E min(X,S) >= x(1-exp(-mu))`.                       (5)

The deterministic mean-capacity value is `min(x,mu)`. If `mu<=x`, its
gap from the right side of (5) is at most `mu exp(-mu)`: the expression
decreases as `x` increases, so set `x=mu`. If `mu>=x`, the gap is at most
`x exp(-mu)<=mu exp(-mu)`. In both cases it is at most `1/e`. Integrate
over thresholds in (3) to obtain (2). The threshold inequality is sharp
for this independent-sampling estimate: a fixed unit hub and many rare
binary leaves whose total mean tends to one have deficit tending to
`1/e`.

## Several stars and the configuration consequence

Choose the discrete packet of each pair **independently across pairs**.
Within a given fluid-star component, distinct vertices belong to
distinct discrete pairs by hypothesis. Their capacities are therefore
independent, including when the hub belongs to a pair. Components can
share a pair, so their optimal fluid profits need not be independent;
linearity of expectation is enough. For `F_q` the total optimal fluid
profit, `A=F_q(1)` the total all-capacity-one fluid profit, and
`r=E R`, summing (2) gives

`E F_q(R) >= F_q(r)-A/e`.                           (6)

Fix a point of `P`, and for each discrete pair choose a feasible packet
law with that point's expected type counts. Such a law exists because
the pair's type-count mean is the projection of a local star law at
either endpoint. Both endpoints of the pair receive the same sampled
packet. The point's fluid vector is feasible at mean residual capacities
`r`, so its fluid profit is at most `F_q(r)`.

Write `B` for the point's expected discrete profit. With probability
`alpha=e/(e+1)`, sample the pair packets independently as above and
route an optimal state-feasible fluid flow. With probability `1-alpha`,
leave all discrete pairs empty and route the all-capacity-one optimal
fluid flow, worth `A`. The resulting distribution consists of globally
feasible mixed patterns and has expected profit at least

`alpha B + alpha(F_q(r)-A/e)+(1-alpha)A`
`=alpha(B+F_q(r)) >= alpha p.x`,                 (7)

because `1-alpha=alpha/e`. Maximizing over the local point proves (1).
The global mixed-pattern hull is compact and downward closed for finite
input, so nonnegative-profit support inequalities imply the claimed
coordinatewise containment.

## Scope relative to prior work

The prior arbitrary-density single-star half-deficit note handles two
endpoints of one discrete pair in the *same* star, but its one-star
coupling cannot be imposed independently around a cycle of stars linked
by shared pair variables. The present condition makes every capacity
within each star independent under one globally consistent product law;
that is why arbitrary cycles of stars are allowed. The price is the
within-star one-endpoint restriction. The theorem is specific to
divisible fluid edges; converting its factor into a uniform asymptotic
integer bound for arbitrary original edge weights requires a separate
fluidization and rounding argument.

The related crossing-prefix proof gives the already-known `A/2` loss
for **one** star with arbitrary paired residual laws, including doubled
leaf contributions. It does not automatically choose compatible
couplings for multiple stars.
