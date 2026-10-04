# Second-phase scratch audit: local policy and a failed additive shortcut

Research only. These arguments are candidates or obstructions within the ongoing
five-hour exploration beginning 2026-10-03 05:21:17 UTC. They do not establish an
unrestricted coloring bound, and nothing here is a manuscript update.

## Exact reduction of the proposed local rule to two stars

For a bipartite fluid graph, let `sum_{e at v} y_e <= D_v <= 1` and
`p_v = 1/4 + 3 D_v/4`. Activate vertices independently. The proposed local rule is

`b_e = min{K y_e/(p_u p_v), 12 y_e}`,

`L_v = sum_{e at v} b_e 1_{both endpoints active}`,

`z_e = b_e 1_{both endpoints active}/max{1,L_u,L_v}`.

It is feasible pointwise and respects the caps. Its desired coordinate guarantee
is `E z_e >= 3 y_e/4`; this is still unproved for K=4/3 (or K=2 or K=3).

Conditional on the two endpoints of a fixed edge being active, their competitor
loads depend on disjoint sets of activation bits: one set lies in each shore.
Consequently those two competitor loads are independent. Parallel fluid edges
should first be aggregated into a single bundle. The whole inequality therefore
reduces to two independent weighted Bernoulli star sums and a common self term.

An equality case is an isolated edge of target `a=1/3`, with both D values equal
to a: both activation probabilities are 1/2, so every feasible rule has expected
flow at most 1/4 = 3a/4. This is a sharp case distinct from the tiny-target cap
case.

For a leaf edge with target a and uncapped tentative coefficient, if its own
tentative load is at least one, Jensen gives a short one-sided bound. Write
`P=1/4+3D/4` for the center probability and `A=1/4+3a/4` for the leaf probability.
The expected competitor tentative load is at most `K(D-a)/P`. Thus

`E z_e/a >= P A/[a + A(D-a)] >= 3/4`,

where the last inequality is exactly

`P A - (3/4)[a + A(D-a)] = (3a/4 - 1/4)^2 >= 0`.

This only handles the stated one-sided, self-load-at-least-one case. It does not
prove the two-star inequality.

## A tempting Jensen shortcut is false

For K=2 and an infinitesimal probe edge between two D=1 centers, suppose one
center has three other edges of target 1/3 and the other four of target 1/4,
with minimal leaf D values. In the zero-probe limit the normalized competitor
loads are

`S_3 = (2/3) Bin(3,1/2)`,

`S_4 = (4/7) Bin(4,7/16)`.

Exact finite summation (the inputs are rational) gives

`E max{1/2,S_3,S_4} = 1.3337182998657227 > 4/3`.

Hence the sufficient expected-denominator inequality
`E max{1,L_u,L_v} <= 8/3` fails for K=2, by continuity also for a sufficiently
small positive probe target after reducing the other incident targets to keep
D=1. This does not refute the original expected-reciprocal inequality.

For K=4/3, even two three-spoke centers give the analogous failure:
`E max{3/4,S_3,S_3'} = 1.34375 > 4/3`.

## Removing internal fluid bundles from a heavy pair

This is a conditional reduction: it becomes useful only if a suitable local
binary allocation policy and the final finite-palette step are proved.

Let alpha=3/4. A heavy pair has a shared random actual residual R in [0,1],
mean `p=1-alpha L=1/4+alpha D`, where `D=1-L` and L is its input heavy load.
Let I be the total target of fluid edges internal to this pair, so I<=D.
Reserve internal edge e the conditional flow

`alpha y_e R/p`.

Its mean is alpha y_e, its cap is at most 3y_e, and the total reservation is at
most R. The remaining shared residual is

`R'=(1-alpha I/p)R`,

with mean `p'=1/4+alpha(D-I)`. Every external target degree is at most D-I.
Thus internal fluid edges can be removed before applying a local external-edge
policy. Given R', average that binary policy over a shared Bernoulli activation
of each pair with conditional success probability R'. The conditional average
has vertex loads at most R', so it gives a feasible real-residual allocation.

For an external probe edge, correlating a third heavy pair's two endpoint bits
affects one competitor load on each end. The function
`(x,y) -> 1/max{1,x,y}` is supermodular, so that correlation has the favorable
sign. Once internal fluid edges are removed, a pair containing a probe endpoint
has no other endpoint-bit effect in the probe's local formula. This explains
why the internal reservation matters; simply applying the original rule with
internal edges present is false, as the physical-rounding agent found.

## The unscaled additive-gap shortcut is false

Let the heavy support be C_10. Give the five edges of one perfect matching M1
weight 3/5 and those of the other perfect matching M2 weight 1. Give every heavy
edge marginal x_e=1/2. Any matching distribution with these marginals must cover
every vertex almost surely, so it is the equal mixture of M1 and M2.

Add a new vertex c on the right shore and fluid edges of unit profit from c to
all five left cycle vertices. The local residual capacities are D_c=1 and
D_v=1/5 at each leaf. Thus F(D)=F(1)=1. Under the forced full heavy law, the
fluid-star value is 1 in state M1 and 0 in state M2, so C_q(x)=1/2.

Therefore the proposed inequality
`C_q(x) >= F_q(D) - F_q(1)/3`
fails (its right side is 2/3). This refutes only that shortcut, not the desired
scaled-marginal claim at alpha=3/4.

Indeed the scaled instance has recourse one in every state under a different
law: choose all of M1 with probability 3/8; with the remaining probability 5/8,
choose uniformly three of the five disjoint unit edges of M2. Every heavy edge
then has marginal 3/8, while the star always has residual capacity at least one.

## Another invalid shortcut

Independent thinning of an arbitrary heavy matching decomposition need not
work. Take two disjoint unit-heavy edges with marginals 1/2, and a unit-profit
fluid edge joining one endpoint of each on opposite shores. A heavy law that
chooses exactly one of the two heavy edges in every state, followed by retaining
it independently with probability 3/4, leaves the fluid edge available with
probability 1/4. The local fluid target is 1/2, whose desired scaled value is
3/8. A better heavy coupling exists; this shows that the choice of decomposition
cannot be ignored.
