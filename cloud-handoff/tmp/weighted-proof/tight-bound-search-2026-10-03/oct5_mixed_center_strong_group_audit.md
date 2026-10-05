# Independent audit of the mixed-center strong-group inequality

5 October 2026. **Passed at the stated per-group scope.** This note
audits the algebra needed for a single fluid star with whole-star load
`S∈[1/2,1]`, a center whose categorical guard weights are at least
`1/2`, and a leaf guard pair **distinct from the center guard pair**.
It proves one strong-group conditional throughput estimate. It does
not assemble the full star theorem or establish a law for several
interacting stars.

Put `alpha=2/3`, `q=(4S−1)/3`, `T=1−q=4(1−S)/3`, and
`c=(2S−1)/(3S)`. Since the center weighted guard target is at most
`1−S` and every center guard type weighs at least `1/2`, its total
presence is at most `2(1−S)`. Thus a virtual center-free bit
`B=1{U>T}` guarantees that the actual center is free, while
`Pr(B=1)=q`. The per-group calculation below assumes the leaf guard
pair has a common-threshold marginal with this virtual bit and that
its categorical type is sampled independently of the threshold
conditional on occupancy.

## The strong group's pointwise flow

Let a profit prefix contain one or two leaves from the same guard
pair, with total target mass `Y<=S`. Let its largest leaf target be
`d=tY`, where `t∈[1/2,1]`. Aggregate the prefix caps at each leaf;
each is at least `K` times that leaf's prefix target. A group is
strong when `KY>=1` (in the intended application `K=12`). Write
`R∈[0,1]` for the common leaf residual.

For one leaf, `t=1` and its cap is at least one, so the group can
carry `R=min(1,R/t)`. For two leaves, the larger leaf has cap at least
`KtY>=t`; the smaller has cap at least `K(1−t)Y>=1−t`.
If `R<=t`, the larger leaf can carry `R`, and the smaller can carry
at least `min(R,1−t)>=R(1−t)/t`; their total is at least `R/t`.
If `R>=t`, the two leaves can carry at least `t+(1−t)=1`.
Thus the group throughput into a fully free center, truncated at one,
is pointwise at least `min(1,R/t)`.

When every leaf guard type has weight `w>=1/2`, occupied residual
`R=1−w<=1/2<=t`, so the lower model gives throughput
`(1−w)/t` when occupied and one when absent. If the pair's total
original presence is `x`, its conditional mean occupied weight is
`mu∈[1/2,1]`, and its weighted target is `a=mu x`, then local
feasibility at the larger leaf gives `a<=1−tY`. The lower model's
expected throughput on `B=1` is exactly

`M=q−[(mu+t−1)/t]*(alpha x−T)_+`.

The penalty factor is nonnegative because `mu,t>=1/2`. Hence at fixed
`mu,t,Y`, the smallest `M` occurs at the largest feasible
`x=min(1,(1−tY)/mu)` (with `x=0` cases trivial).

## Proof of `M>=1/3+cY`

First observe

`q−(1/3+cY)=(2S−1)(2−Y/S)/3>=0`,

so if `alpha x<=T` the claim is immediate.

**Case 1: `mu<=1−tY`.** The worst feasible `x` is one. At fixed
`t,Y`, the penalty increases with `mu`, so its worst feasible value
is the boundary `mu=1−tY`. There the penalty factor is `1−Y` and
`alpha−T=2(2S−1)/3`. Therefore

`M=q−(1−Y)(alpha−T)=1/3+Y(alpha−T)
  >=1/3+cY`,

because `alpha−T>=c` is equivalent to `S>=1/2` (with equality
understood at `S=1/2`).

**Case 2: `mu>=1−tY`.** The worst feasible
`x=(1−tY)/mu`. At fixed `S,t,mu`, the function

`M−(1/3+cY)
 = q−[(mu+t−1)/t]*(alpha(1−tY)/mu−T)_+
   −1/3−cY`

is concave in `Y`: it is a linear function minus a nonnegative
multiple of the positive part of an affine function. Its minimum on
the feasible interval `Y∈[(1−mu)/t,S]` occurs at an endpoint.
The lower endpoint is exactly Case 1's `x=1` boundary. It remains to
check `Y=S`. If the threshold overlap is nonpositive, the first
observation proves the claim. Otherwise `M>=2S/3` is equivalent to

`(mu+t−1)[2(1−tS)−4mu(1−S)] <= t mu(2S−1)`.       (★)

Set `v=1−S`. Feasibility `mu>=1−tS` gives
`0<=v<=min(1/2,(mu+t−1)/t)`. For fixed `mu,t`, the right side of
(★) minus its left side is affine in `v`, so it suffices to check
the endpoints of this interval.

At `v=0`, the difference is

`A=mu(3t−2)+2(1−t)^2>=0`.

For `t>=2/3`, this is immediate. For `t∈[1/2,2/3]`, the coefficient
of `mu` is nonpositive, so the minimum over `mu<=1` is at `mu=1`,
where `A=t(2t−1)>=0`.

At upper endpoint `v=1/2`, one has `S=1/2`, `T=alpha`, and `x<=1`;
the threshold overlap `alpha x−T` is zero, so (★) is trivial.
At the alternative upper endpoint `v=(mu+t−1)/t`, one has
`mu=1−tS` and `x=1`, already covered by Case 1. Directly,
the penalty factor is then `1−S`, and
`(1−S)(alpha−T)<= (2S−1)/3` follows from `S>=1/2`.
Thus (★) holds throughout the feasible domain, proving
`M>=1/3+cY` for every strong group.

A 300,000-sample numerical domain check over
`S∈[1/2,1]`, `Y∈[0,S]`, `t,mu∈[1/2,1]`, at the worst feasible
`x`, found no negative gap; this is secondary to the exact algebra.

## Scope boundaries

The proof uses both `w>=1/2` (so occupied `R<=t` and the penalty is
nonnegative) and `KY>=1` (so the group's caps supply the pointwise
`min(1,R/t)` flow). It uses a leaf guard pair distinct from the
center's pair; the center's own guard partner as a leaf has a different
dependence and is not covered by this calculation. The full-star
product/weak-group assembly remains a separate step.
