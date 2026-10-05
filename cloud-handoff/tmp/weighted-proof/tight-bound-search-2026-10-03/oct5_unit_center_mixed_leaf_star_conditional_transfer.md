# Conditional center coupling for one capped mixed-leaf fluid star

5 October 2026. **Proof candidate for independent audit.** One fluid star has a center guarded by a *unit-weight* heavy pair (possibly several categorical physical identities) and arbitrarily many leaves guarded by other heavy pairs with **arbitrary categorical weights in `[0,1]`**. The center's heavy partner may itself be a leaf of this star. Heavy simple support is a matching; any other leaf guard pair may contribute one or two leaves. Fluid identities may be parallel and have caps `C_e≥12y_e`. The local vertex rows hold. At scale `alpha=2/3`, there is a single q-independent heavy law with exact categorical heavy marginals and a conditional feasible fluid policy with exact fluid marginals. The law is tailored to this one star. It is not yet a globally consistent law for a forest of stars linked by shared leaf guards, nor does it handle a nonunit center guard.

Let `S=Σ_e y_e≤1` be the **whole-star** target load at the center. Its original unit-heavy presence `x_0` obeys `x_0≤1−S`. Put `A=1+2S` and `p=A/3=1−alpha(1−S)`. Draw an auxiliary bit `B` with `P(B=1)=p`. This bit represents a pessimistic center-free event, not an additional physical edge. Conditional on `B=1`, draw a fresh uniform `U_0` on `(alpha(1−S),1)`; conditional on `B=0`, draw it on `(0,alpha(1−S))`. Select an actual center heavy identity iff `U_0≤alpha x_0`, choosing its categorical identity in proportion to its original `x_h`. Since `x_0≤1−S`, **`B=1` guarantees that the actual center is free**. The physical heavy identity marginals are `alpha x_h`.

For each other heavy pair `i` that supplies star leaves, independently conditional on `B` draw `U_i` uniformly from the same interval as `U_0`. Occupy that pair iff `U_i≤alpha x_i`, and then choose its categorical heavy type `h` with probability `x_h/x_i`. Thus every physical leaf-heavy identity has marginal `alpha x_h`, and distinct leaf groups are independent conditional on `B`. Each pair's joint distribution with `B` is the two-source common-threshold distribution, even though different leaf pairs do not share the same `U_i`.

Fix a profit prefix that does not include any edge to the center's own heavy partner. Write `s=Σ_prefix y_e≤S`, and group its leaves by heavy pair. Group `i` has one or two leaves and prefix target mass `Y_i`, with `Σ_i Y_i=s`. Its common residual allowance `D_i` is at least `Y_i/2`. Let `R_i` be its actual residual under the sampled categorical state. The two-source common-threshold moment inequality (as proved in `oct4_mixed_heavy_comonotone_degree2_transfer.txt`) applied to the auxiliary unit blocker of original presence `1−S` gives

`E[B R_i] ≥ (1+2S D_i)/3 ≥ (1+S Y_i)/3`.

Consequently, conditional on `B=1`,

`E[R_i | B=1] ≥ (1+S Y_i)/A =: q_i`.

Set `c_i=min(1,12Y_i)`. Given a sampled residual, the maximum prefix throughput from group `i` into a free center is `Σ_{leaf ℓ in i}min(R_i,C_{iℓ})`, where `C_{iℓ}` is the sum of the prefix identity caps at that leaf. Truncate this at one and call it `T_i∈[0,1]`. The elementary inequalities `min(r,C)≥r min(1,C)` and `Σℓ min(1,C_{iℓ})≥min(1,Σℓ C_{iℓ})` show **pointwise** `T_i≥c_i R_i`, since `Σℓ C_{iℓ}≥12Y_i`. Hence `E[T_i|B=1]≥c_i q_i`. Conditional independence of the leaf pairs yields

`E[star prefix throughput] ≥ p [1−Π_i(1−c_i q_i)]`.       (1)

Indeed on `B=1` the center has unit residual capacity and its prefix optimum is `min(1,Σ_i T_i)≥1−Π_i(1−T_i)`; outcomes with `B=0` are simply discarded.

The following elementary product bound completes all prefixes **under this one law based on total S**:

`Π_i(1−c_i q_i) ≤ 1−2s/A`, for `0≤s≤S≤1`.             (2)

To prove it, call a group weak when `Y_i<1/12`. Its factor is at most `exp(−12Y_i/A)`, since `q_i≥1/A`. A strong group has `c_i=1` and factor at most `S(2−Y_i)/A`. If all groups are weak, the product is at most `exp(−12s/A)≤1−2s/A`: put `z=12s/A≤4`; the concave function `1−z/6−exp(−z)` is nonnegative at `z=0` and `z=4`, hence throughout `[0,4]`.

If strong groups have total mass `T>0`, their factors can be merged: for `a+b≤1`,

`[S(2−a)/A][S(2−b)/A] ≤ S(2−a−b)/A`,

because `S/A≤1/3` and `(2−a)(2−b)≤3(2−a−b)`. Let weak mass be `W=s−T`. Then the product is at most `[S(2−s+W)/A]exp(−12W/A)`. The numerator `S(2−s+W)exp(−12W/A)` decreases in `W` (its logarithmic derivative is at most `1−4<0`), so it is at most `S(2−s)`. Finally `S(2−s)≤A−2s` is equivalent to `s(2−S)≤1`, true because `s≤S≤1` and `S(2−S)≤1`. This proves (2).

If a prefix includes fluid identities to the center's own heavy partner, let their total target be `y_0` and the external-group prefix target be `t=s−y_0`. On `B=1`, both center and that partner are fully free. Their internal bundle can supply `c_0=min(1,12y_0)` units. If `y_0≥1/12`, this alone gives expected prefix throughput at least `p=(1+2S)/3≥2s/3`. If `y_0<1/12`, then `c_0=12y_0` and, pointwise on `B=1`,

`min(1,c_0+X)≥c_0+(1−c_0)min(1,X)`.

The external-group calculation above applies to the same fixed law with prefix mass `t≤S`; hence expected throughput is at least `p c_0+(1−c_0)2t/3`. Subtracting the target `2s/3` leaves

`y_0[12p−8t−2/3] = y_0[10/3+8(S−t)]≥0`.

Thus every prefix has expected throughput at least `2s/3`. A fixed star state admits a greedy descending-profit fluid flow that maximizes every prefix throughput, so layer-cake integration proves the support inequality for every nonnegative profit vector under this **same** heavy law. Compact downward-closed support-function separation gives a conditional capped fluid policy with exact `2y_e/3` coordinate means. All heavy identities already have exact `2x_h/3` marginals.

Two limitations are essential. First, a guard pair can supply leaves to two distinct stars; the two stars' center-bit conditionals may demand incompatible laws for that shared pair, so this one-star construction cannot be glued without another consistency argument. Second, if the center heavy weight is below one, the auxiliary event `B=1` need not be contained in an actual unit-free center event at the pessimistic probability `p`; its partial residual requires a separate argument. The proof does not use or claim the fixed `3/4` independent plus `1/4` comonotone law.
