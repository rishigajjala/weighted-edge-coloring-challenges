# Three-scenario median lemma and half-integral-heavy exact 3/2 inclusion

**Status: proved scoped theorem; arbitrary heavy marginals remain open.** This is for the repeatable-type mixed model: heavy edges of weights `w_e in (1/2,1]` are discrete, fluid edges have divisible nonnegative amounts, and all graph supports may be arbitrary loopless multigraphs. No original physical-edge integer-coloring assertion follows from this note.

For nonnegative fluid profits `q`, define the fractional fluid value at vertex capacities `r in [0,1]^V` by

`F_q(r)=max{q·t:t>=0, sum_{f incident v}t_f<=r_v for each v}`.

Its dual is

`F_q(r)=min{sum_v r_v b_v:b>=0, b_u+b_v>=q_f for each fluid edge f=uv}`.

## Three-scenario median lemma

Suppose `r^1,r^2,r^3 in [0,1]^V` and `D>=0` satisfy

`r^1_v+r^2_v+r^3_v >= 1+2D_v` for every vertex `v`.

Then, for **every** nonnegative fluid-profit vector `q`,

`F_q(r^1)+F_q(r^2)+F_q(r^3) >= 2 F_q(D)`.       (1)

**Proof.** Choose an optimal dual cover `b^i` for each `F_q(r^i)` and let `b_v` be the median of the three numbers `b^1_v,b^2_v,b^3_v`. The median vector is a feasible cover: for any fluid edge `uv`, at least two indices have `b^i_u<=b_u`, and at least two have `b^i_v<=b_v`; their index sets intersect, so some `i` has both inequalities and therefore `b_u+b_v>=b^i_u+b^i_v>=q_{uv}`.

At any vertex, at most one of the three `b^i_v` is strictly below `b_v`. Its corresponding capacity is at most one. All remaining prices are at least `b_v`, hence

`sum_i r^i_v b^i_v >= b_v (sum_i r^i_v-1) >= 2D_v b_v`.

Summing over vertices and applying weak duality to the feasible cover `b` gives `sum_i F_q(r^i)>=2 sum_v D_v b_v>=2F_q(D)`. ∎

The constant and the three-scenario form are sharp as a general capacity inequality: on one fluid edge `uv`, take `r_u=(1,1,0)`, `r_v=(0,1,1)`, and `D_u=D_v=1/2`. The three values sum to one, while `2F_1(D)=1`.

## Exact mixed inclusion for half-integral heavy coordinates

Let `(x,y)` satisfy at each vertex

`sum_{e heavy incident v}x_e<=1`,

`sum_{e heavy incident v}w_e x_e + sum_{f fluid incident v}y_f<=1`,

with `x_e in {0,1/2,1}` for every heavy type. Put `D_v=1-sum_{e heavy incident v}w_e x_e`. The multigraph consisting of `2x_e` copies of each heavy type has maximum degree at most two, so it has a proper three-edge-coloring. Let `A_1,A_2,A_3` be the heavy matchings in its color classes. Each original heavy type appears in exactly `2x_e` of these three matchings. With physical residual capacities

`r^i_v=1-sum_{e in A_i:e incident v}w_e`,

we have `r^i_v in [0,1]` and

`sum_i r^i_v=3-2sum_{e heavy incident v}w_e x_e=1+2D_v`.

The median lemma gives `sum_i F_q(r^i)>=2F_q(D)>=2q·y` for every nonnegative `q`, because `y` is feasible at capacity `D`. The Minkowski average of the three conditional fluid packing polytopes is compact, convex, and coordinatewise downclosed. Support-function separation therefore supplies fluid flows `t^i` feasible at `r^i` with

`(t^1+t^2+t^3)/3=(2/3)y` coordinatewise.

Choose one of the three physical patterns `(A_i,t^i)` uniformly. Heavy type `e` has mean `(2x_e)/3`, and fluid type `f` has mean `(2y_f)/3`. Thus the exact coordinatewise inclusion `(2/3)(x,y)` in the physical mixed-pattern hull holds for all locally feasible points whose **heavy** coordinates are half-integral. No restriction is imposed on fluid support, fluid amounts, or heavy weights other than `(1/2,1]`.

## Remaining obstruction

General local points need not have half-integral heavy coordinates, and decomposing their heavy vector into half-integral degree-polytope vertices does not automatically decompose the prescribed fluid vector under the corresponding conditional residual capacities. The median proof needs a *joint three-state heavy schedule* with exact edge multiplicities `2x_e`, so it cannot simply be applied to arbitrary rational `x`. Establishing an appropriate random three-scenario analogue, or a fluid-compatible decomposition into half-integral heavy points, would close the unrestricted mixed-model 3/2 inclusion. Neither step is proved here.

Even optimizing a support function does **not** force a half-integral heavy solution. Take disjoint heavy edges `e_1=ua` of weight `3/5` and profit `1`, and `e_2=vb` of weight `9/10` and profit `1/2`; add one unit-profit fluid edge `uv`. For fixed `x_1,x_2 in [0,1]`, the best fluid amount is `y=min(1-(3/5)x_1,1-(9/10)x_2)`. Maximizing `x_1+(1/2)x_2+y` gives the unique heavy optimum `x_1=1,x_2=2/3`, with `y=2/5` and value `26/15`. (For fixed `x_2`, increasing `x_1` has slope at least `1-3/5>0`; with `x_1=1`, the objective increases in `x_2` up to `2/3` and decreases thereafter.) Restricting both heavy coordinates to `{0,1/2,1}` gives at most `33/20`, attained at `(1,1/2)`. Thus a proof cannot merely select a half-integral local optimum.

Likewise, replacing three states by an arbitrary `3N`-color heavy schedule loses the median premise. With `N=2`, two disjoint unit-heavy stars can give residual profiles `r_u=(1,1,1,0,0,0)` and `r_v=(0,0,0,1,1,1)` under a poorly aligned six-color schedule. Their local residual capacities are `D_u=D_v=1/4`, but a fluid edge `uv` has zero capacity in every color, whereas `4F_1(D)=1`. A better aligned schedule exists; this example only shows that Shannon edge coloring without further coordination is insufficient.
