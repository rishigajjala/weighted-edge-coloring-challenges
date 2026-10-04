# Two paired stars joined by a fluid bridge: an uncapped hybrid transfer

4 October 2026. Scratch-only scoped theorem. This proves the fixed `3/4` independent plus `1/4` comonotone heavy law works for an overlapping fluid support beyond a disjoint star forest. The first proof treats uncapped fluid; the final section extends it to conditional caps `C_e>=12y_e`.

Take three disjoint unit-heavy pairs `A=(a_0,a_1)`, `B=(b_0,b_1)`, `C=(c_0,c_1)`. The five fluid endpoint bundles are `a_0b_0,a_1b_0,b_1c_0,b_1c_1,b_0b_1`; each bundle may contain parallel fluid identities. Write `x=D_A,y=D_B,z=D_C` for the local residual degree allowances, each in `[0,1]`; all target fluid degrees at each port are at most its pair's allowance. The graph may be nonbipartite because a heavy edge together with two spokes forms a triangle. Each fluid identity may carry any amount up to the unit vertex capacities when its endpoints are free.

At scale `alpha=2/3`, put `p_d=(1+2d)/3`. With probability `3/4`, free heavy pairs independently with probabilities `p_x,p_y,p_z`. With probability `1/4`, use one common uniform variable and free pair `i` iff `U<=p_i`. Both modes select each heavy pair with the prescribed scaled marginal `alpha(1-D_i)`; any parallel heavy identities can be chosen conditionally in their prescribed proportions.

**Claim.** For every locally feasible fluid target and every nonnegative fluid-profit vector, the expected optimal fluid recourse under this *same* heavy law is at least `alpha` times the target profit. Consequently support-function separation gives exact scaled fluid marginals under the fixed heavy law for this uncapped five-edge support.

Let `a` be the larger of the two `A`-spoke profits, `c` the larger of the two `C`-spoke profits, and `b` the bridge profit. If the bridge target is `r`, the two spoke target totals are at most `min(y-r,2x)` and `min(y-r,2z)`. Thus the target profit is bounded above by the convex homogeneous function

`g(a,c,b)=max_{0<=r<=y} [b*r+a*min(y-r,2x)+c*min(y-r,2z)]`.       (1)

For the random free indicators `I_A,I_B,I_C`, the exact optimal *uncapped* state recourse is

`I_B * max(b,a*I_A+c*I_C)`.                                           (2)

We prove `E(2)>=(2/3)g` for all `a,c,b>=0`. Exchange `A,C` to assume `a>=c`. Formula (2) is linear in the profit vector on the cones cut by `b=c`, `b=a`, and `b=a+c`; their nonnegative extreme rays are

`(a,c,b)=(0,0,1),(1,0,0),(1,1,0),(1,0,1),(1,1,1),(1,1,2)`.

Since `g` is convex and homogeneous, it suffices to check these six rays.

Put `R(d,e)=P(pair with allowance d and pair with allowance e are both free)`. If `m=min(d,e), M=max(d,e)`, the hybrid law gives

`R(d,e)=(1+2m)(1+M)/6`.                                               (3)

The needed two-pair inequality is

`R(d,e)>=(2/3)*min(e,2d)`.                                             (4)

For `e<=d`, multiply by six and use `d>=e` to reduce to `(1+2e)(1+e)-4e=1-e+2e²>=0`. For `d<=e<=2d`, the difference after multiplying by six is `1+2d-3e+2de`, decreasing in `e`; at `e=min(2d,1)` it is respectively `(1-2d)^2` or `4d-2`, both nonnegative. For `e>=2d`, the difference is `(1+2d)(1+e)-8d`, increasing in `e` and equal to `(1-2d)^2` at `e=2d`. This proves (4).

The rays now have simple checks. On `(0,0,1)`, `(1,0,1)`, and `(1,1,2)`, expected recourse is respectively `p_y,p_y,2p_y`, while `g` is `y,y,2y`; use `p_y>=(2/3)y`. On `(1,0,0)`, expected recourse is `R(x,y)` and `g=min(y,2x)`, so use (4). On `(1,1,0)`, both sides add the corresponding `A` and `C` two-pair inequalities.

On the only genuinely interacting ray `(1,1,1)`, put `m=min(x,z)`. Formula (1) gives `g=y+min(y,2m)`, while (2) has expectation `p_y+T`, with `T=P(A,B,C all free)`. Monotonicity in the larger of `x,z` and the hybrid formula imply

`T >= (3/4)*p_m²*p_y+(1/4)*min(p_m,p_y)
   = R(m,y)-(3/4)*p_m*p_y*(1-p_m)
   >= R(m,y)-3/16`.

Finally `p_y-(2/3)y=1/3`, so by (4)

`p_y+T >= (2/3)y+1/3+R(m,y)-3/16
         >= (2/3)[y+min(y,2m)]+7/48`.

The interacting ray has strict slack. This completes the six-ray proof and the claim.

The equality in (4) at `(d,e)=(1/2,1)` corresponds to the familiar two-spoke paired-leaf star: its center target is already one, so a positive bridge cannot be added without changing the local allowances. This isolates the sharp star at the boundary of this five-edge family and explains why simply linking two copies did not amplify it.

## Capped extension at `C_e>=12y_e`

Now give every fluid edge `e` a conditional one-color cap `C_e>=12y_e`, where `y_e` is its local target. The cap may exceed one, but the unit vertex capacities make any excess irrelevant. The same fixed heavy law still gives expected optimal capped-fluid recourse at least `2/3` of every local fluid target profit.

For fixed fluid profits, let `a` be the optimum capped recourse value on the two `A` spoke bundles when `A,B` are both free; define `c` analogously for the two `C` spoke bundles; and let `b` be the optimum full-free capped profit on the bridge bundle. When `B` is free, one can either take the bridge or take both available spoke-star optima. Thus statewise recourse is **at least** `I_B max(b,I_A*a+I_C*c)`; equality is not needed because splitting center capacity between the bridge and spokes could do better.

Let `s_A,s_C,r` be the local target amounts on the `A` spokes, `C` spokes, and bridge, and put `delta=1/12`. Local capacities give

`s_A<=min(y-r,2x)`, `s_C<=min(y-r,2z)`, `0<=r<=y`.               (5)

If `s_A>0`, multiply each targeted `A`-spoke flow by `t=min(12,1/s_A)`. The resulting full-free star flow respects its center capacity because `t*s_A<=1`, each leaf capacity because its scaled total target is at most `t*s_A<=1`, and every identity cap because `t*y_e<=12y_e<=C_e`. Its profit is `t` times the local `A`-spoke profit. Hence that target profit is at most `a*max(s_A,delta)`; if `s_A=0` it is zero and the same upper bound holds. Likewise the `C`-spoke target profit is at most `c*max(s_C,delta)`. Scaling the bridge bundle's targeted flow by `min(12,1/r)` gives bridge target profit at most `b*max(r,delta)` by the same argument.

The capped upper bound is therefore

`a*max(s_A,delta)+c*max(s_C,delta)+b*max(r,delta)`.             (6)

For fixed target amounts, (6) is linear in `(a,c,b)`. The lower bound on expected recourse is the same piecewise-linear function of `(a,c,b)` as in (2). Therefore the same six profit rays suffice; on each cone the recourse is linear and any vector is a nonnegative combination of its rays.

On ray `(1,0,0)`, (5) and (4) give `R(x,y)>=(2/3)min(y,2x)`. Also `R(x,y)>=1/6>(2/3)delta`, so `R(x,y)>=(2/3)max(s_A,delta)`. Ray `(1,1,0)` follows by adding the `A` and `C` inequalities. Ray `(0,0,1)` follows from `p_y=(2/3)y+1/3` and `r<=y`: `p_y>=(2/3)max(r,delta)`.

On ray `(1,0,1)`, (5) gives `s_A+r<=y`, and the two `delta` floors in (6) cost at most `2delta`. Thus its target profit is at most `y+2delta`, while recourse is `p_y=(2/3)y+1/3`; the extra `(2/3)*2delta=1/9` is covered. On ray `(1,1,2)`, (5) gives `s_A+s_C+2r<=2y`, and the four floors cost at most `4delta`; recourse `2p_y=(2/3)*2y+2/3` covers the extra `(2/3)*4delta=2/9`.

For `(1,1,1)` put `m=min(x,z)` and `T=P(A,B,C all free)`. From (5), with `t=y-r`, one has

`s_A+s_C+r <= y-t+min(t,2m)+min(t,2max(x,z))
             <= y+min(y,2m)`.                                   (7)

The three floors in (6) add at most `3delta`, whose `2/3`-scaled cost is exactly `1/6`. We need the strengthened triple-event bound

`p_y+T >= (2/3)[y+min(y,2m)]+1/6`.                             (8)

Here is an algebraic check. Monotonicity in the larger of `x,z` reduces to `x=z=m`. Set `p=(1+2m)/3`, `q=(1+2y)/3`; then

`T >= (3/4)*p*p*q+(1/4)*min(p,q)`.

As `p_y-(2/3)y=1/3`, (8) is equivalent to

`T >= (2/3)*min(y,2m)-1/6`.                                     (9)

If `y<=m`, then `min(p,q)=q` and `min(y,2m)=y`. The lower bound for `T` increases with `m`, so set `m=y`. Multiplying the difference in (9) by six gives

`6*[q*(3q*q+1)/4 - (4y-1)/6]
   = (4y^3+6y^2-6y+5)/3 >0`,

since the numerator is `4y^3+6(y-1/2)^2+7/2`.

If `y>=m`, put `s=min(y,2m)`. Multiplying the difference in (9) by 36 gives

`F(m,y)=(1+2m)*[(1+2m)*(1+2y)+3]-24s+6`.

For `y<=2m`, its derivative in `y` is `2(1+2m)^2-24<0`; for `y>=2m`, the derivative is `2(1+2m)^2>0`. Hence the minimum over `y∈[m,1]` occurs at `y=min(2m,1)`. If `m<=1/2`, substitution `y=2m` yields

`F(m,2m)=2(2m-1)(4m²+7m-5)>=0`

because both factors in the product are nonpositive on `[0,1/2]`. If `m>=1/2`, substitution `y=1` gives

`F(m,1)=6(m+2)(2m-1)>=0`.

This proves (8), including equality at `m=1/2,y=1`, and pays for the three cap floors. All six rays are established, so the capped `2/3` transfer follows for this exact five-edge support.

Numerical checks preceded the proof. `oct4_two_paired_stars_bridge_scan.py` examined all 4,149 local extreme targets on a six-value grid for each allowance and optimized every profit direction by exact-state cutting planes. Its maximum local/recourse ratio was `3/2`, attained with the bridge absent and only one star profitable. `oct4_unit_guard_hybrid_octapolar.py` likewise sampled 4,592 local extreme targets on a three-pair octahedral fluid support; the maximum was `3/2` and again reduced to one two-spoke star. Those scripts used uncapped recourse; the capped extension is proved above by the `delta` scaling argument, not by the diagnostics. Nothing here proves the hybrid transfer for arbitrary fluid graphs.
