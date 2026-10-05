# Independent audit: conditional center law for one mixed-leaf star

5 October 2026. I audited
`oct5_unit_center_mixed_leaf_star_conditional_transfer.md` against the
stated one-star model. **The proof passes at precisely that scope.**
It gives a q-independent categorical-heavy law and, by support-function
separation, exact fluid means at scale `2/3`. It does not give a common
law for several interacting stars or a nonunit guarded center.

## The auxiliary bit and physical guard marginals

Put `S=Σ_star y_e`, `t_0=(2/3)(1−S)`, and `p=1−t_0=(1+2S)/3`.
The construction first samples `B=1` with probability `p`, then draws
`U_0` uniformly in `(t_0,1)` if `B=1` and in `(0,t_0)` otherwise.
Consequently `U_0` is uniform on `(0,1)` and
`B=1{U_0>t_0}`. Because the actual unit guard at the center has total
target `x_0<=1−S`, its occupied event `U_0<=(2/3)x_0` is contained in
`B=0`. Thus `B=1` guarantees one unit of actual center capacity. A
center physical identity `h` is selected with probability
`(2/3)x_0*(x_h/x_0)=(2/3)x_h` when `x_0>0`.

For each leaf guard pair, `U_i` is sampled independently conditional
on `B` from the same interval as `U_0`. Each `U_i` is marginally
uniform on `(0,1)`, and its categorical heavy identity `h` is selected
with probability `(2/3)x_h`. Moreover
`B=1{U_i>t_0}` for every leaf pair, so `(B,R_i)` has exactly the
two-source common-threshold marginal law. Different leaf pairs and
their conditional type draws are independent given `B`, which is the
independence required in the product step. Two leaves belonging to one
guard pair correctly share one residual `R_i` and are grouped together.
Pairs with target zero are treated as always unoccupied; the formulas
extend by continuity when `S=0` or `x_i=0`.

## Prefix moment and group throughput

For a profit prefix of mass `s<=S`, a group of one or two leaves has
prefix mass `Y_i`; its common allowance satisfies `D_i>=Y_i/2`.
Writing `a_i=1−D_i=x_i E[W_i|occupied]`, the key moment can also be
checked directly. The virtual center blocker has threshold `t_0`,
so

`E[B R_i]=p−(2/3)E[W_i|occupied]*(x_i−1+S)_+`.

The inequality `(x_i−1+S)_+<=S x_i` follows from `x_i<=1`.
Therefore

`E[B R_i]>=p−(2/3)S a_i=(1+2S D_i)/3
          >=(1+S Y_i)/3`.

Dividing by `p=(1+2S)/3` gives the claimed conditional mean
`q_i=(1+S Y_i)/(1+2S)`. Crucially this uses **whole-star** `S`, not
the prefix `s`; the law is fixed before the profit vector is chosen.

Let `C_{iℓ}` be the sum of prefix caps at leaf `ℓ` in group `i`.
Its available prefix throughput, truncated at center capacity one, is
`T_i=min(1,Σ_ℓ min(R_i,C_{iℓ}))`. For `0<=R_i<=1`,
`min(R_i,C_{iℓ})>=R_i min(1,C_{iℓ})`, and
`Σ_ℓ min(1,C_{iℓ})>=min(1,Σ_ℓ C_{iℓ})`. Hence

`T_i>=R_i min(1,Σ_ℓ C_{iℓ})>=R_i min(1,12Y_i)=c_iR_i`.

Thus `E[T_i|B=1]>=c_i q_i`. The prefix optimum on `B=1` is
`min(1,Σ_i T_i)`, and for `T_i∈[0,1]` it is at least
`1−Π_i(1−T_i)`. Conditional independence yields equation (1) of
the candidate, with no need to assume independence unconditionally.

## Product bound and its endpoints

Write `A=1+2S`. For weak groups `Y_i<1/12`, `c_i=12Y_i`, and
`1−c_iq_i<=exp(−12Y_i/A)`. If every group is weak, put
`z=12s/A<=12S/(1+2S)<=4`. The function
`g(z)=1−z/6−exp(−z)` is concave on `[0,4]`, with `g(0)=0` and
`g(4)=1/3−exp(−4)>0`, so
`Π_i(1−c_iq_i)<=exp(−z)<=1−2s/A`.

For a strong group `Y_i>=1/12`, its factor is at most
`1−q_i=S(2−Y_i)/A`. The stated merge inequality is valid for
`a+b<=s<=1`: with `t=a+b`,
`3(2−t)−(2−a)(2−b)=2−t−ab>=0`, while
`S/A<=1/3`. Hence all strong groups merge to total mass `T`.
If weak mass is `W=s−T`, the product is at most
`[S(2−s+W)/A]exp(−12W/A)`. Its logarithmic derivative in `W`
is `1/(2−s+W)−12/A<=1−4<0`, so the expression is largest at
`W=0`. The final comparison
`S(2−s)<=A−2s` is equivalent to `s(2−S)<=1`, true because
`s<=S<=1` and `S(2−S)<=1`. Thus equation (2) holds for every
`0<=s<=S<=1`, including empty prefix and `S=1` boundaries.

Combining equations (1) and (2) gives expected prefix throughput at
least `p*(2s/A)=2s/3`. On a star, greedy descending-profit flow
maximizes all prefix throughputs simultaneously, so layer-cake gives
the all-profit support inequality under this same law. Finite-state
compact convex downward-closed separation then gives one conditional
fluid policy with coordinate means exactly `(2/3)y_e`.

## Scope retained

The law is tailored to the one star's full `S`. A guard pair whose
endpoints are leaves of two stars could receive incompatible
conditional distributions from their two center bits; no forest
gluing follows. A center guarded by a weight below one can have
positive residual on `B=0` but need not be physically free on `B=1`
at the virtual unit-blocker probability used above. The proof does
not establish the fixed `3/4` independent plus `1/4` comonotone law,
arbitrary branching, or a finite physical palette.
