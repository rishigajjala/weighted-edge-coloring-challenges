# Independent audit of the capped five-edge two-star bridge

4 October 2026. This checks the capped extension in `oct4_two_paired_stars_bridge_hybrid_analytic.md` independently. **Verdict:** the stated `2/3` one-color transfer is valid for that exact five-fluid-edge family, assuming its three disjoint unit-heavy pairs and local target constraints. This says nothing about arbitrary fluid support or a physical integer palette.

## Model and cap reduction

The fluid edges are two spokes from pair `A` to `b0`, two spokes from pair `C` to `b1`, and the bridge `b0b1`, with `B=(b0,b1)` the central unit-heavy pair. Pair-free indicators are `I_A,I_B,I_C`. Denote pair allowances by `x,y,z in[0,1]`, bridge target by `r`, and the two spoke target totals by `s_A,s_C`. Local feasibility gives

`0<=r<=y`, `0<=s_A<=min(y−r,2x)`, `0<=s_C<=min(y−r,2z)`.

Fix nonnegative fluid profits and caps `C_e>=12 target_e`. Let `a,c` be the optimum full-free **capped** profit on the A and C two-spoke stars separately, and `b=q_bridge min(C_bridge,1)`. If `B` is free, choosing either the bridge-only flow or both noninterfering spoke-star optima is feasible. Hence state recourse is at least `I_B max(b,I_A a+I_C c)`. It can be larger when splitting a central port between bridge and spokes; using a lower bound is sound.

For `s_A>0`, multiply the target flow on each A spoke by `t_A=min(12,1/s_A)`. The scaled flow respects each edge cap because `t_A target_e<=12target_e<=C_e`, the center capacity because `t_A s_A<=1`, and the leaf capacity because each target_e<=s_A. Its profit is `t_A` times the A-target profit, so the latter is at most `a/t_A=a max(s_A,1/12)`. At `s_A=0`, target profit is zero and the same upper bound remains true. The C side is identical. If `C_bridge>=1`, bridge target profit `q_bridge r` is at most `b r`; if `0<C_bridge<1`, `r/C_bridge<=1/12`, so it is at most `b/12`; if `C_bridge=0`, then `r=0` and both are zero. Thus total target profit is bounded by

`a max(s_A,delta)+c max(s_C,delta)+b max(r,delta)`, `delta=1/12`.

This handles caps greater than one correctly: a unit endpoint makes their effective bridge cap one, and the spoke scaling still respects a larger edge cap. It also handles zero target/cap cases without division by zero.

## Exhaustive profit cones

Swap A and C, including their allowances and target totals, so `a>=c>=0`. For a fixed target `(s_A,s_C,r)`, the upper bound above is linear in `(a,c,b)`. The statewise lower bound is linear on the four cones separated by `b=c`, `b=a`, and `b=a+c`. Every point on each cone is a nonnegative combination of the advertised six rays, as the following explicit decompositions show:

* If `0<=b<=c<=a`: `(a,c,b)=(a−c)(1,0,0)+(c−b)(1,1,0)+b(1,1,1)`.
* If `0<=c<=b<=a`: `(a,c,b)=(a−b)(1,0,0)+(b−c)(1,0,1)+c(1,1,1)`.
* If `0<=c<=a<=b<=a+c`: `(a,c,b)=(a−c)(1,0,1)+(a+c−b)(1,1,1)+(b−a)(1,1,2)`.
* If `0<=c<=a` and `b>=a+c`: `(a,c,b)=(b−a−c)(0,0,1)+(a−c)(1,0,1)+c(1,1,2)`.

On boundaries and at `(0,0,0)`, these remain valid with zero coefficients. Thus six ray checks prove the inequality for every nonnegative profit vector; no separate convexity assumption about the capped target function is needed.

## Pair and triple probabilities

For the fixed `3/4` independent plus `1/4` common-uniform hybrid law at scale `2/3`, a pair with allowance `d` is free with `p_d=(1+2d)/3`, and two-pair joint freedom is

`R(d,e)=[(1+2 min(d,e))(1+max(d,e))]/6`.

The draft's three-case proof verifies `R(d,e)>=(2/3)min(e,2d)` for all `d,e in[0,1]`; the boundary differences are respectively `1−e+2e²`, `(1−2d)²` or `4d−2`, and `(1−2d)²`, all nonnegative on their stated case domains. Also `R(d,e)>=1/6`, which pays any one `2/3*delta=1/18` floor.

The easy rays check as follows:

* `(1,0,0)` uses the pair bound plus `R>=1/6` to pay `max(s_A,delta)`; `(1,1,0)` adds the A and C copies.
* `(0,0,1)` has recourse `p_y=2y/3+1/3`, covering `max(r,delta)` since `r<=y` and `delta=1/12`.
* `(1,0,1)` has recourse `p_y`, while `max(s_A,delta)+max(r,delta)<=y+2delta`; the scaled floor charge `4delta/3=1/9` is below the `1/3` free-probability slack.
* `(1,1,2)` has recourse `2p_y`, while `max(s_A,delta)+max(s_C,delta)+2max(r,delta)<=2y+4delta`; its scaled floor charge `8delta/3=2/9` is below the `2/3` slack.

For `(1,1,1)`, let `m=min(x,z)`, `t=y−r`, and `T=P(I_A=I_B=I_C=1)`. Since the larger-side spoke total is at most `t`, the un-floored target satisfies

`s_A+s_C+r<=y−t+t+min(t,2m)<=y+min(y,2m)`.

The three `delta` floors cost at most `3delta`, scaled by `2/3` to exactly `1/6`. State recourse is `p_y+T`, so it remains to prove

`T >= (2/3)min(y,2m)−1/6`.

The triple-free probability increases in `x,z`; its worst case for fixed `m` is `x=z=m`. Write `p=(1+2m)/3`, `q=(1+2y)/3`; then `T>=3p²q/4+min(p,q)/4`. If `y<=m`, set `m=y` to minimize this bound. Six times the difference from `(2/3)y−1/6` is `(4y³+6y²−6y+5)/3 = [4y³+6(y−1/2)²+7/2]/3>0`.

If `y>=m`, put `s=min(y,2m)`. Thirty-six times the difference is

`F(m,y)=(1+2m)[(1+2m)(1+2y)+3]−24s+6`.

On `y<=2m`, its derivative is `2(1+2m)²−24<0`; on `y>=2m`, its derivative is `2(1+2m)²>0`. Thus the minimum over `y∈[m,1]` occurs at `y=min(2m,1)`. If `m<=1/2`, substitution `y=2m` gives `2(2m−1)(4m²+7m−5)>=0` because both factors are nonpositive. If `m>=1/2`, substitution `y=1` is on the **`s=y` branch** and gives `6(m+2)(2m−1)>=0`. I separately checked these factorizations symbolically. Equality in the latter branch occurs at `m=1/2,y=1`; all zero/endpoint allowance cases are included.

Therefore all six rays hold, and the capped five-edge `2/3` transfer follows by support-function separation under the same fixed heavy law. The scope is exactly the three unit-heavy pairs and five fluid edge positions; no generalized star or graph theorem is inferred.

As a transcription check, I also sampled 20,000 feasible allowance/target vectors, random nonnegative profits, and caps between `12` and `60` times each target, and evaluated the eight heavy-free states directly. The smallest numerical recourse-minus-`2/3`-target gap was about `0.000375`; this check is not used in the proof.
