# Audited heterogeneous-heavy capped transfer on fluid degree-two support

4 October 2026. This strengthens the earlier unit-guard hybrid
max-degree-two calculation. It is a divisible one-color convex-hull
statement, not an integer physical-edge coloring result or an arbitrary
fluid-support theorem.

## Statement

The simple support of categorical discrete edges is a matching. An endpoint pair
`i` may have physical types of arbitrary weights in `(0,1]`, with
probabilities `x_{i,h}` summing to `x_i≤1`. Write its conditional mean
weight `mu_i`, expected local heavy load `a_i=x_i mu_i`, and residual
allowance `D_i=1−a_i`. Unguarded vertices have `D=1` and residual one.
Let divisible-fluid target `y` satisfy `Σ_{e∋v}y_e≤D_v`, with at most
two positive physical fluid coordinates at every vertex, and let
`C_e≥2y_e`. Then there is one one-color law with exact marginals
`(2/3)x_{i,h}` on every heavy identity and exact mean `(2/3)y_e` on
every fluid coordinate, without a bipartiteness assumption.

## Pure comonotone heavy law

Set `alpha=2/3`. Take one uniform `U∈[0,1]` for all heavy pairs.
Occupy pair `i` iff `U≤alpha x_i`; when occupied, choose a type
independently across occupied pairs with conditional probabilities
`x_{i,h}/x_i`. Thus each heavy identity has marginal `alpha x_{i,h}`.
The residual at both endpoints of pair `i` is
`R_i=1−B_i W_i∈[0,1]`. We have `E R_i=1−alpha a_i`.

For distinct pairs `i,j`, conditional type independence and shared
occupancy threshold give the exact identity

`E(R_i R_j)
 =1−alpha(a_i+a_j)+alpha min(a_i mu_j,a_j mu_i)`.

Since `x_i≤1`, we always have `mu_i≥a_i`, without a lower bound on
type weights. Therefore the cross term is at least `a_i a_j`, giving
the symmetric lower bound

`L(s,t)=(1+2st)/3`, for `s=D_i,t=D_j`.

For an edge within the same discrete pair, Jensen gives
`E W_i²≥mu_i²`, hence
`E R_i²≥1−(4/3)a_i+(2/3)a_i mu_i
          ≥1−(4/3)a_i+(2/3)a_i²=L(D_i,D_i)`.
An unguarded endpoint `D=1` satisfies the bound exactly:
`E R_j=(1+2D_j)/3=L(1,D_j)`. The function `L` is
nondecreasing in both arguments and always at least `1/3`.

## Exact edgewise fluid policy and row feasibility

For a fluid edge `e=uv`, write `M_e=E(R_uR_v)`. In a sampled heavy
state route

`f_e=alpha y_e R_uR_v/M_e`.

Its coordinate mean is exactly `alpha y_e`. Since `M_e≥1/3` and
`R_uR_v≤1`, it obeys `f_e≤2y_e≤C_e`.

Fix vertex `v` with allowance `s=D_v`. Every incident positive
coordinate has `y_e≤s` and the other endpoint allowance at least
`y_e`. By monotonicity of `L`, `M_e≥L(s,y_e)`. Thus, in every state,

`Σ_{e∋v}f_e ≤ R_v Σ_{e∋v} g_s(y_e)`,

where

`g_s(y)=alpha y/L(s,y)=2y/(1+2sy)`.

This function is concave and increasing throughout `[0,s]`. With at
most two positive incident fluid coordinates and
`S=Σ y_e≤s`, pad with zero and apply Jensen:

`Σ g_s(y_e)≤2g_s(S/2)≤2g_s(s/2)
              =2s/(1+s²)≤1`.

The last inequality is `(1−s)^2≥0`. Hence total fluid load at `v` is at most its actual
residual `R_v` in every sampled heavy state. This proves one-color
feasibility and all exact marginals. The law and fluid rule are
independent of profits.

The same calculation supplies a local sufficient condition at a vertex
of arbitrary positive-target degree `k≥2`: Jensen gives
`Σg_s(y_e)≤k g_s(s/k)=2s/(1+2s²/k)`. If this is at most one at
every vertex, the same global coordinate policy works. In particular,
degree-three branch vertices with `D_v≤(3−√3)/2` pass; for unbounded
degree the condition is `D_v≤1/2`. This does not cover high-residual
diffuse stars, where pure comonotonicity can lose too much recourse.

## Limits

The derivative/Jensen argument uses at most two positive fluid
coordinates per vertex. For three or more, diffuse branching may make
the direct product rule overload a vertex; the audited unit-heavy star
proof uses adaptive recourse instead. Discrete supports beyond a matching,
exact physical tiny-edge stocks, and an
integer palette remain outside this statement.
