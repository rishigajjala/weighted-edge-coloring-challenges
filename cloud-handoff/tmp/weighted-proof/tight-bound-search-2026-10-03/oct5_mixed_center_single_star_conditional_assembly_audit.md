# Mixed-center single-star conditional transfer: assembly audit

5 October 2026. This is a scoped, audited convex-hull result for **one**
divisible-fluid star. It does not synchronize distinct stars or transfer to
physical tiny-edge palettes.

Let the heavy-edge simple support be a matching. At each heavy pair there is
a categorical choice of at most one physical heavy type; all positive heavy
weights lie in `[1/2,1]`. The fluid support is one star (parallel fluid
identities are allowed), with center `c`, target `y`, and total target load
`S=Σ_e y_e≤1`. The local point has heavy marginals `x_h` and fluid loads
`y_e`, with `Σ_{h∋v}w_h x_h+Σ_{e∋v}y_e≤1`. Each fluid edge has a per-state
cap `C_e≥K y_e`. A support-function law may depend on the nonnegative profit
vector, but the heavy law below does not.

Fix `δ∈(0,1/2]`, `K=4/δ`, `α=2/3`, and `β=α/(1+2δ)`. There is a joint
feasible law with exact heavy marginals `β x_h` and fluid marginals `β y_e`.
For `S>1/2+δ`, the construction first obtains factor `α` and then thins
heavy and fluid marginals to `β`. For `S≤1/2+δ`, the common-quantile product
flow gives factor `β` directly, as described below. The result is for a
single fluid star; shared heavy pairs between several stars are not handled.

## High-load center law

Assume `S>1/2+δ`. Center heavy presence `x_c` is at most `2(1−S)`, because
each center heavy weight is at least `1/2`. Set

`q=(4S−1)/3`, `T=1−q=4(1−S)/3`, and `a=2S−1`.

Draw `U` uniformly on `[0,1]`. Put the center heavy pair in a heavy state
when `U≤α x_c`, and sample its type according to the normalized `x_h`.
The event `B={U>T}` has probability `q` and guarantees that the center,
including its heavy partner if that partner is a fluid leaf, is fully free.
For every other heavy pair, draw a separate `U_i`, independently across pairs
conditional on `B`: uniform on `[0,T]` if `B=0`, uniform on `[T,1]` if `B=1`.
Put pair `i` in a heavy state iff `U_i≤α x_i`, drawing its type independently
conditional on occupancy. The unconditional `U_i` is uniform, so each
physical heavy type has its exact `α x_h` marginal. The distinct leaf-pair
sources are independent conditional on `B`.

For a profit threshold, let `Y_i` be the target mass in the prefix from
one leaf guard pair, comprising one or two fluid leaves, and let
`t_i=max_j y_{ij}/Y_i∈[1/2,1]`. Its common residual is `R_i`. Put
`c_i=min(1,KY_i)`. From the individual caps `C_e≥K y_e`, the pair can
carry, into a fully free center, at least

`c_i min(1,R_i/t_i)`.

Indeed, after grouping parallel prefix identities at a leaf, its available
cap is at least `KY_i` times that leaf's fraction of `Y_i`. For two leaves,
`min(R,t)+min(R,1−t)≥min(1,R/t)` for `t≥1/2`; scaling both caps by
`c_i≤1` yields the displayed bound. The one-leaf case is immediate.

If `Y_i≥1/K` (strong), the independent algebra note
`oct5_mixed_center_strong_group_audit.md` proves

`E[B min(1,R_i/t_i)]≥1/3 + [(2S−1)/(3S)]Y_i`.

The proof uses `w≥1/2`: occupied residual `1−w≤1/2≤t_i`, making the
throughput linear in the occupied heavy weight. For completeness, if pair
presence is `x`, its mean occupied weight is `μ`, and `x μ≤1−t_iY_i`, the
exact lower-model moment is

`q − [(μ+t_i−1)/t_i](αx−T)_+`.

It is at least the displayed bound for all feasible parameters. A weak
group (`Y_i<1/K`) has `c_i=KY_i`, hence its moment is at least `K Y_i/3`.

Conditional on `B=1`, write the lower-model group throughputs as independent
`Z_i∈[0,1]`. Pointwise,

`min(1,Σ_i Z_i)≥1−Π_i(1−Z_i)`.

Thus its expectation is at least `q(1−Π_i r_i)`, where each strong factor
is at most

`r(Y)=r_0(2−Y/S)`, `r_0=(2S−1)/(4S−1)≤1/3`,

and a weak factor is at most `exp[−K Y/(3q)]`. For masses with sum at most
`S`, one checks `r(Y_1)r(Y_2)≤r(Y_1+Y_2)`. Also
`K/(3q)≥1/S≥1/(2S−Y)` for `K≥3` and `Y≤S`, so weak masses can be absorbed
into a strong factor. If any strong group occurs, the product is at most
`r(s)`, where `s=Σ_iY_i≤S`, giving

`q[1−r(s)]=1/3+[(2S−1)/(3S)]s≥2s/3`.

If every group is weak, the product is at most `exp[−K s/(3q)]`. The
resulting lower bound `q[1−exp(−K s/(3q))]` is concave in `s`, zero at
zero, and at least `2S/3` at `s=S`: it suffices that
`exp[−K S/(4S−1)]≤r_0`. For `S≥1/2+δ`, `S/(4S−1)≥1/3` and
`r_0≥2δ/3`. With `K=4/δ`,
`exp[−K S/(4S−1)]≤exp[−4/(3δ)]≤3δ/(4e)≤2δ/3`.

If the center's heavy partner is itself a fluid leaf in the prefix, its
target is `y_0` and it is wholly free on `B=1`; its cap supplies the
deterministic baseline `c_0=min(1,K y_0)`. The other leaf pairs have prefix
mass `s_*=s−y_0` and yield at least `2s_*/3`. The pointwise inequality
`min(1,c_0+Z)≥c_0+(1−c_0)min(1,Z)` gives expected recourse at least
`q c_0+(1−c_0)2s_*/3`. This exceeds `2s/3`: if `c_0=1`, use
`q≥2S/3`; otherwise `c_0=K y_0` and
`q−2s_*/3≥(2S−1+2y_0)/3`, while `K(2S−1)≥8`.

Every profit prefix therefore has expected unit-profit recourse at least
`2/3` of its target prefix mass. Fractional-knapsack greediness on a star
gives the layer-cake identity for arbitrary nonnegative fluid profits: the
optimal star recourse is the integral of its prefix rank values. Hence the
same heavy law satisfies every fluid support-function inequality. Convex
separation supplies a conditional fluid-flow law with exact marginals
`α y_e` and caps `C_e`; recourse can be randomized without changing the
heavy law. Any surplus flow can be discarded. Uniformly thinning all heavy
types and the chosen fluid flow by `1/(1+2δ)` preserves feasibility and
gives exact factor `β`.

## Low-load branch

If `S≤1/2+δ`, every fluid vertex has target load at most `S`. The
common-quantile heavy law at marginals `αx` has residual product moments
`E[R_uR_v]≥1/3`. The explicit flow

`f_e=α y_e R_uR_v / E[R_uR_v]`

has exact means `α y_e`, cap `f_e≤2y_e`, and statewise load at each
vertex at most `2S R_v≤(1+2δ)R_v`. Scale this fluid flow by
`1/(1+2δ)`, then independently delete each sampled heavy edge with that
same probability of retention. The deletion only enlarges residual
capacities. Heavy and fluid marginals become exactly `βx,βy`, with cap
`2y_e≤K y_e`.

## Boundaries

The proof is for divisible fluid, categorical heavy types on a matching
simple support, and one fluid star. It does not establish a common law for
many stars with unequal whole-star loads: their center-free events would
have different thresholds, while the leaf-pair product estimate needs
conditional independence at each star. It also does not give an integer
coloring or a result for unrestricted heavy support.
