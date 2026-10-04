# A two-blocker activation lemma, and its exact limitation

This note concerns an **already coupled factor relaxation**, not the original
vertex-local configuration LP. In particular, it does not prove a new global
bound for arbitrary weighted edge coloring.

Let `Z=(Z_1,Z_2)` be any pair of binary blocker states with marginals
`E Z_i=x_i`. Let `B_1,B_2` be independent binary states with
`P(B_i=1)=3*x_i/4`. For every nonnegative function `f` that is
nonincreasing in each argument,

    E f(B_1,B_2) >= (3/4) E f(Z_1,Z_2).                 (1)

Proof: A nonnegative antitone function on `{0,1}^2` is a nonnegative
combination, by its threshold layers, of the indicators of the five
nonempty downsets: all states, `Z_1=0`, `Z_2=0`, both zero, and at least
one zero. The first three satisfy (1) immediately. For the both-zero
indicator, suppose `x_1>=x_2`. Its expectation under `Z` is at most
`1-x_1`, whereas its expectation under `B` is

    (1-3*x_1/4)(1-3*x_2/4)
      >= (1-3*x_1/4)^2
      >= (3/4)(1-x_1),

because the last difference is `(3*x_1-2)^2/16`. For the at-least-one-zero
indicator, the `Z` expectation is at most
`min(1,2-x_1-x_2)`. Write `s=x_1+x_2`. The `B` expectation is
`1-9*x_1*x_2/16 >= 1-9*s^2/64`. If `s<=1`, this is at least
`55/64>3/4`. If `1<=s<=2`, subtracting `(3/4)(2-s)` gives at least
`(-32+48*s-9*s^2)/64`, a concave quadratic whose endpoint values are
`7/64` and `28/64`. This proves (1). The factor `3/4` is sharp for the
both-zero indicator at `x_1=x_2=2/3` with `Z_1=Z_2`.

One application is to a matching of binary heavy blocker edges whose
deletion splits the remaining graph into vertex-disjoint factors, each
incident to at most two blockers. Conditional on the blockers, the best
internal factor profit is an antitone function `f` of those two bits.
If a *strengthened* local relaxation supplies a joint feasible factor
pattern law with consistent blocker marginals, independent activation
at `3*x_i/4` and conditional factor optimization yield at least `3/4`
of the strengthened relaxation's profit. Blocker profits themselves
scale exactly by `3/4`.

The original vertex-local configuration LP does **not** in general
provide a feasible joint pattern law inside a factor. At blocker means
zero, a unit triangle has vertex-local value `3/2` and global factor
value `1`. The relation triangle with a unit direct edge and two fluid
spokes has the same local obstruction: direct mean `1/2` and each spoke
mean `1/2` give local value `3/2` with unit profits, while its best
one-color factor profit is `1`. Thus applying (1) to that LP would
silently multiply two distinct gaps. Any route beyond the known general
`3/2` lower bound through these blocker-factor networks must identify
how factor-internal triangle incompatibility interacts with the global
blocker correlations; the pair-activation lemma alone does not settle it.
