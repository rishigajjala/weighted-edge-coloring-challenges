# Audited scoped candidate: capped two-thirds fluid transfer for unit heavy guards and disjoint stars

**Scope.** The heavy edges all have weight one. Their simple support is a
matching; parallel physical heavy identities at one pair are allowed, with a
categorical local law of total presence `x_P≤1`. The divisible fluid support
is a vertex-disjoint star forest (its union with the heavy edges need not be
bipartite). A fluid edge `e` has conditional one-color cap `C_e≥12y_e`,
where `y_e` is its target marginal. Local feasibility gives
`x_{P(v)}+Σ_{e∋v}y_e≤1` at every guarded vertex, with `x_{P(v)}=0` when
unguarded. This note proves a `2/3` convex-hull inclusion for this scoped
fluid model. It does not prove an integer physical-edge coloring theorem or
the unrestricted heavy-support/tiny-edge bound.

## One fixed heavy law

Put `alpha=2/3`. Use a global mode coin. With probability `3/4`
(independent mode), sample the categorical heavy state independently for
each heavy pair, selecting physical identity `h` with probability
`alpha x_h`. With probability `1/4` (comonotone mode), sample a single
uniform `U∈[0,1]`; make pair `P` free iff `U≤p_P=1−alpha x_P`, and,
when occupied, select identity `h` conditionally with probability
`x_h/x_P`. Every physical heavy edge has marginal `alpha x_h` in both
modes. Because all heavy weights are one, the pair's capacity state is
binary and identical at its two endpoints. The heavy law is independent of
fluid profits and caps.

We show that, for every nonnegative fluid-profit vector `q`, the expected
optimal capped star-forest fluid recourse under this heavy law is at least
`alpha Σ_e q_e y_e`. Downward closure and support-function separation then
give a conditional fluid policy with exact marginals `alpha y_e` under the
same heavy law. The stars are vertex-disjoint, so their recourse objectives
add even when a heavy pair links two stars.

## One star and one profit prefix

Fix one star and a prefix of its fluid edges in decreasing profit order.
Write `s=Σ_prefix y_e≤1`. The center's free probability is at least
`p_s=(1+2s)/3`, since its original heavy presence is at most `1−s`.
Lower free probabilities are pessimistic in both modes, so use equality.
For the moment suppose the center's heavy partner is not a leaf in this
prefix. Group prefix leaves by heavy pair. A group has one or two leaves;
write its target mass `Y_i`, set `d_i=Y_i/2`, and pessimistically give its
pair free probability `p_i=(1+2d_i)/3`. This is valid because the actual
residual allowance at each of a pair's leaves is at least its incident
target, hence at least `Y_i/2` when there are two leaves. A singleton or
unguarded leaf only has more availability. Thus `Σ_i d_i=s/2`.

The cap available from a free group is at least
`c_i=min(1,12Y_i)=min(1,24d_i)`. Indeed, the prefix caps sum to at least
`12Y_i`, each of the at most two free leaves has unit capacity, and the
center needs at most one unit in total. For independent group indicators
`A_i`, define `P` by

`E min(1,Σ_i c_i A_i) ≥ 1−P`,

using `min(1,Σ a_i)≥1−∏(1−a_i)` for `0≤a_i≤1`. A **strong** group has
`d_i≥1/24`, so `c_i=1` and contributes
`1−p_i=(2/3)(1−d_i)` to `P`. A **weak** group has `c_i=24d_i<1`
and contributes at most

`1−c_i p_i ≤ exp(−c_i p_i) ≤ exp(−8d_i)`.

The independent-mode expected prefix recourse is at least
`p_s(1−P)`. If a strong group of maximal `d_i=m` exists, the
comonotone-mode recourse is at least its activation probability
`p_m=(1+2m)/3`, because `p_s≥p_m`. If all groups are weak but
`s≥1/12`, then `Σ_i c_i=12s≥1`; the event `U≤1/3` activates the
center and every group, so comonotone recourse is at least `1/3`.

We check that the mode mixture gives at least `2s/3` in all cases.

* **All weak, `s≤1/12`.** Here `Σ_i c_i=12s≤1`, so the independent
  recourse is linear and at least `p_s Σ_i c_i/3=4p_s s`.
  Its `3/4` mode weight alone contributes `3p_s s≥s≥2s/3`.

* **All weak, `s≥1/12`.** The above bounds reduce the desired inequality
  to `exp(−4s)≤(4−2s)/[3(1+2s)]`. In fact
  `(4−2s)exp(4s)−3(1+2s)` starts at `1` for `s=0` and has derivative
  `exp(4s)(14−8s)−6≥0` on `[0,1]`.

* **Exactly one strong group.** Let its value be `m`. Since the other
  groups are weak,
  `P≤(2/3)(1−m)exp(−8(s/2−m))`. The required condition is
  `P≤(4−2s+2m)/[3(1+2s)]`. The ratio of the stated upper bound for
  `P` to this threshold increases with `m∈[0,s/2]`: its logarithmic
  derivative is
  `8−1/(1−m)−2/(4−2s+2m)>0`.
  At `m=s/2`, the inequality reduces to
  `(1+s)^2/6≥2s/3`, equivalent to `(1−s)^2≥0`.

* **At least two strong groups.** Absorb all weak mass `d` into one
  nonmaximal strong group of current mass `b`. The inequality
  `exp(−8d)≤(1−b−d)/(1−b)` holds because `b+d≤s/2≤1/2` and
  `log(1−d/(1−b))≥−d/(1−b−d)≥−2d`.
  Then repeatedly merge nonmaximal strong groups, using
  `(2/3)(1−a−b)≥(4/9)(1−a)(1−b)` for `a+b≤1/2`.
  This yields `P≤(4/9)(1−m)(1−s/2+m)`. The required inequality is
  `4(1+2s)(1−m)(1−s/2+m)≤3(4−2s+2m)`.
  Right minus left equals
  `4(1−s)(2−s)+2(1−s)(3+2s)m+4(1+2s)m²≥0`.

If the center's heavy partner **is** a prefix leaf, write its prefix
target as `y_0` and the remaining target as `t=s−y_0`. The center and
this leaf are free together. If `y_0≥1/12`, that leaf's cap is at
least one, so expected recourse is at least `p_s≥2s/3`. Otherwise put
`c_0=12y_0<1`. Pointwise,
`min(1,c_0+Z)≥c_0+(1−c_0)min(1,Z)` when the center is free.
Apply the preceding external-group result to target `t`, with center
free probability `p_t`; the actual `p_s≥p_t` dominates it in both
modes by coupling the center threshold. Expected recourse is at least

`c_0 p_s+(1−c_0)(2t/3)
 =2t/3+4y_0(1+2y_0) ≥2s/3`.

## Profits and scope of the conclusion

For a fixed capacity state of a star, filling fluid edges in decreasing
profit order maximizes every prefix throughput simultaneously. Hence the
weighted optimum is the exact layer-cake sum of prefix throughputs. The
prefix bound above integrates to expected profit at least
`(2/3)Σ_e q_e y_e` for any nonnegative `q`; summing over disjoint
stars proves the stated support-function inequality. A single global
mixture coin and a single global comonotone `U` suffice across all stars.

The proof uses binary residual capacities of unit heavy guards at several
places, especially the activation probabilities and the cap-throughput
argument. It does **not** extend directly to heterogeneous heavy weights:
comonotone real-residual quantile profiles need not be stochastically
ordered by their means. The arbitrary-fluid-support case remains open for
this fixed law.
