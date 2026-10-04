# Capped hybrid transfer for two paired stars with distinct centers

4 October 2026. Scratch-only **scoped theorem candidate pending independent audit**. The fixed unit-heavy `3/4` independent plus `1/4` comonotone law transfers every capped fluid target on this distinct-center bridge family at scale `2/3`. This does not cover arbitrary fluid graphs. An earlier attempt to invoke the capped-star theorem on the lower recourse model was invalid; the direct OR-event argument below replaces it.

Take four disjoint unit-heavy pairs `A=(a_0,a_1)`, `B=(b_0,b_1)`, `C=(c_0,c_1)`, `D=(d_0,d_1)`. The fluid endpoint bundles are `a_0b_0,a_1b_0,b_0c_0,c_0d_0,c_0d_1`; parallel fluid identities in each bundle are allowed. Every fluid identity has conditional cap `C_e>=12y_e`, where `y_e` is its local target. Write `x=D_A`, `b=D_B`, `c=D_C`, `d=D_D` for the local residual degree allowances. All heavy edges have weight one and occupy both ports of their pair when selected. The one common mode coin is `3/4` independent scaled pair activation plus `1/4` comonotone scaled pair activation, with free probability `p_t=(1+2t)/3` for a pair with allowance `t`.

**Claim.** Under that fixed heavy law, every locally feasible fluid target has a conditional fluid policy with exact `2y_e/3` marginals. The proof checks every nonnegative fluid-profit direction and uses support-function separation.

Let `a` and `d_0` denote the optimum full-free capped profits of the left and right two-spoke stars, respectively, and let `h` denote the optimum full-free capped profit of the bridge bundle. To avoid using `d_0` for a pair vertex below, write these three effective profits as `(u,v,h)`. If `I_A,I_B,I_C,I_D` denote free indicators, a statewise lower bound on capped recourse is

`F >= I_B I_A*u + I_C I_D*v + I_B I_C*(h-I_A*u-I_D*v)_+`.       (1)

Indeed, choose both available star optima or choose the bridge; if one center is busy only its other star may operate. For `u>=v`, the right side is linear on the cones cut by `h=v`, `h=u`, and `h=u+v`, whose rays are

`(u,v,h)=(0,0,1),(1,0,0),(1,1,0),(1,0,1),(1,1,1),(1,1,2)`.

Fix the physical target/caps and, within each of the three bundle groups, scale all profits uniformly. The full-free group optimum and its target profit both scale linearly. Thus checking these effective-profit rays proves the support inequality for every original profit vector. Exchanging the left/right stars handles `u<v`.

The proof uses two event inequalities. The first is the two-pair bound (5) below. The second, for three independent/comonotone pair-free indicators, is the **OR bound**:

`H(a,b,c)=P(B free and (A free or C free))
          >= (2/3)[max(s,delta)+max(r,delta)]`,                   (OR)

whenever `s+r<=b`, `s<=2a`, `r<=c`, and `delta=1/12`. Here `a,b,c` are the allowances of the two-leaf pair, center pair, and one-leaf pair, and `s,r` are the corresponding target group amounts. The `max` terms arise from the cap scaling argument given after (2).

To prove (OR), first ignore the `delta` floors. The largest possible `s+r` is `g_OR=min(b,2a+c)`. Let `p_t=(1+2t)/3`. The law gives

`H=(3/4)p_b(p_a+p_c-p_a p_c)+(1/4)min(p_b,max(p_a,p_c))`.

We claim the uniform margin `H-(2/3)g_OR>=7/96`. Truncate `a` to at most `b/2` and `c` to at most `b`; this leaves `g_OR` unchanged and can only decrease `H`. For fixed `b`, each one-sided derivative of `H` with respect to `a` or `c` is at most `1/2`. Below the boundary `2a+c=b`, the derivatives of `(2/3)g_OR` are `4/3` and `2/3`, so increasing `a` or `c` toward the boundary decreases the margin. Above the boundary, lowering them toward it decreases `H` while `g_OR=b` stays fixed. Hence the minimum occurs on `c=b-2a`, `0<=a<=b/2`.

On this boundary `b>=a,c`, so the comonotone term is at least `p_a/4`. Direct expansion yields

`36[H-(2/3)b-1/18]
 >= 8(1+2b)a²+(2-12b-8b²)a+6-10b+8b² =: F(a,b)`.

The quadratic's discriminant complement is `4AC-B²=4P(b)` with

`P(b)=47+28b-124b²+80b³-16b⁴`.

Writing `t=1-b` gives `P=15+44t+20t²-16t³-16t⁴>=15+32t>=15`, since `t³,t⁴<=t²<=t` on `[0,1]`. Completing the square, `F>=P/[8(1+2b)]>=15/24=5/8`. Thus `H-(2/3)g_OR>=1/18+5/288=7/96`, with equality at `b=1,a=3/8,c=1/4`.

If at least one of `s,r` is at least `delta`, the `max` floors cost at most one `delta`, or `(2/3)delta=1/18<7/96` after scaling. If both are below `delta`, their floored sum is at most `2delta=1/6`, whose scaled value is `1/9`; meanwhile `H>=R(a,b)>=1/6`. This proves (OR).

We now verify the six rays. Let `s_A,s_D,r` be total target fluid amounts on the left spokes, right spokes, and bridge. The local degree constraints give

`s_A<=min(b-r,2x)`, `s_D<=min(c-r,2d)`, `0<=r<=min(b,c)`.      (2)

As in the same-center bridge proof, scaling each group's target flow by `min(12,1/s)` shows its local target profit is at most its effective full-free profit times `max(s,delta)`. On the `(1,1,1)` ray the target profit is therefore at most

`max(s_A,delta)+max(s_D,delta)+max(r,delta)`.                   (3)

Ignoring the `delta` floors for the moment, the largest `s_A+s_D+r` allowed by (2) is exactly

`g=min(b,2x)+min(c,2d)+min((b-2x)_+,(c-2d)_+)`.                (4)

To see this, increasing bridge amount `r` first uses simultaneous spare center capacity; once either star begins losing a unit for each added bridge unit, the sum stops increasing, and after both begin losing it decreases.

Put `R(s,t)=P(pairs with allowances s,t both free)`. The hybrid law gives

`R(s,t)=(1+2min(s,t))*(1+max(s,t))/6`.                         (5)

We use `R(s,t)>=(2/3)min(t,2s)` and `R(s,t)>=1/6`. For `t<=s`, the first inequality reduces after multiplying by six to `1-t+2t²>=0`. For `s<=t<=2s`, its difference is `1+2s-3t+2st`, decreasing in `t` and nonnegative at `t=min(2s,1)`; for `t>=2s`, it is increasing in `t` and equals `(1-2s)²` at `t=2s`. The second inequality follows from both free probabilities being at least `1/3`.

The ray's expected recourse lower bound is

`E=R(x,b)+R(d,c)+Q`, where `Q=P(B,C free and A,D busy)`.       (6)

We prove the **uniform margin**

`E >= (2/3)g+1/8`.                                              (7)

First, if `x>b/2`, lower `x` to `b/2`; this leaves (4) unchanged and can only reduce recourse under both activation modes. Likewise lower `d` to `c/2` if needed. We may assume `x<=b/2`, `d<=c/2`. Put `U=b-2x>=0`, `V=c-2d>=0`. Direct expansion of (5) gives the strengthened pair inequality

`R(x,b)-(2/3)*(2x) = U/3+(1-2x)*(1-b)/6`,                   (8)

and its right-star counterpart. Subtracting `(2/3)g` from the two pair terms of (6), using (4), leaves

`|U-V|/3 + [(1-2x)*(1-b)+(1-2d)*(1-c)]/6`.

Drop the nonnegative first term. Since `x<=b/2` and `d<=c/2`, the remainder is at least `[(1-b)^2+(1-c)^2]/6`. The independent-mode part of `Q` is

`(1+2b)*(1+2c)*(1-x)*(1-d)/27`,

at least `f(b)*f(c)/27` for `f(t)=(1+2t)*(1-t/2)=1+3t/2-t²`. The comonotone-mode part is

`[min(b,c)-max(x,d)]_+/6`,

at least `[min(b,c)-max(b,c)/2]_+/6`. Thus the margin in (7) is bounded below by

`L(b,c)=((1-b)^2+(1-c)^2)/6 + f(b)*f(c)/27
        + [min(b,c)-max(b,c)/2]_+/6`.                            (9)

Here is an exact two-variable positivity certificate for `L>=1/8`. By symmetry assume `b<=c`.

If `b<=c/2`, the last term vanishes. The derivative of the other terms with respect to `b` is negative throughout this range: `-(1-b)/3+f'(b)f(c)/27<0`, using `b<=1/2`, `f'(b)<=3/2`, and `f(c)<=25/16`. Hence `L(b,c)>=L(c/2,c)`. Exact simplification gives

`L(c/2,c)-1/8=(c-1)*(2c^3-7c²+37c-53)/216>=0`,

because `c-1<=0` and the cubic is at most `2+37-53=-14` on `[0,1]`.

If `c/2<=b<=c`, write `b=c(1+t)/2`, `u=1-c`, with `0<=u,t<=1`. Exact expansion and regrouping gives

`432[L(b,c)-1/8]
 = (1-u)*6t(2t+1) + u*(42-22t-14t²)
   + u²[(1-u)(58+22t+20t²)+u(60+14t+10t²)]
   + 4u⁴(t+1)² >=0`.

Every displayed term is nonnegative; in particular `42-22t-14t²>=6`. Equality is attained at `(b,c)=(1/2,1)` or symmetrically `(1,1/2)`, with leaf allowances `(x,d)=(1/4,1/2)` in the corresponding order. This proves (7).

Finally pay the cap floors in (3). If at least one of `s_A,s_D,r` is at least `delta`, the total excess of its three `max(s,delta)` terms over `s_A+s_D+r` is at most `2delta=1/6`. Scaling by `2/3` costs at most `1/9<1/8`, so (7) pays it. If all three amounts are below `delta`, (3) is at most `3delta=1/4`, and its scaled value is at most `1/6`; meanwhile (6) is at least `R(x,b)+R(d,c)>=1/6+1/6=1/3`. Hence the `(1,1,1)` ray holds.

The remaining rays use only the two-pair bound and (OR). On `(0,0,1)` the lower model has value `R(b,c)` and the target is bounded by `max(r,delta)`; (5) implies `R(b,c)>=(2/3)min(b,c)` and `R(b,c)>=1/6>(2/3)delta`. On `(1,0,0)`, the corresponding inequality is `R(x,b)>=(2/3)min(b,2x)` plus the same `1/6` floor bound. The `(1,1,0)` ray adds the two spoke inequalities. The `(1,0,1)` ray is exactly (OR) with allowances `(a,b,c)=(x,b,c)` and target groups `(s,r)=(s_A,r)`. On `(1,1,2)` the lower-model state value is the sum of two OR indicators,

`I_B*(I_A or I_C)+I_C*(I_D or I_B)`.

Apply (OR) once at center `B` to groups `(s_A,r)`, and once at center `C` to groups `(s_D,r)`. Their target upper bounds add to `max(s_A,delta)+max(s_D,delta)+2max(r,delta)`, exactly the capped upper bound on this ray. Every ray is verified, completing the support-function claim.

The `1/8` hard-ray margin shows why a blanket charge of all three cap floors would fail: it would cost `1/6`. Charging only floors on *small* target groups is essential. The theorem remains limited to this five-bundle fluid support and four matching heavy pairs.
