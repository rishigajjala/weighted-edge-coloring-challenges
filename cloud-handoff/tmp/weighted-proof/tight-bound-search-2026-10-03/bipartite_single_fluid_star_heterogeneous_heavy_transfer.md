# Interim: one bipartite fluid star, arbitrary heavy center and heterogeneous heavy support

Status: scoped proof independently audited in the research session; the user's five-hour exploration requirement means this is an interim result, not a claim for the unrestricted weighted-edge-coloring problem. This note treats uncapped divisible fluid. It extends the heavy-free-center star argument to a star whose center may be heavy.

## Statement

Let the combined multigraph be bipartite. Categorical heavy edge types `h` have weights `w_h in [1/2,1]` and local marginals `x_h>=0` with `sum_{h incident v}x_h<=1`. Their one-color selected set is a matching. Let uncapped divisible fluid edges form **one star** with center `c`, leaves `v_i`, and locally feasible loads `y_i`, so `sum_{h incident v}w_hx_h+sum_{i: v incident cv_i}y_i<=1` at every vertex. Heavy support may be arbitrary, including parallel heavy types and heavy edges from `c` to its own leaves. Then `(3/4)x_h,(3/4)y_i` lie in the convex hull of one-color mixed states.

We prove the support inequality for each nonnegative fluid-profit vector `q`. Order leaves by decreasing profit, `v_1,v_2,...`. Write `D_v=1−sum_{h incident v}w_hx_h` and unweighted heavy-free marginal `a_v=1−sum_{h incident v}x_h`.

## Full heavy law with two nested free-event relations

Set

`b_1=min(a_c,a_{v_1})`,

`b_2=min(a_c−b_1,a_{v_2})`.

If the star has only one leaf, omit `b_2`; if it has no leaves the claim is trivial. The vector consisting of heavy coordinates `x_h` and two **ordinary matching** spoke coordinates `b_1,b_2` satisfies each bipartite vertex degree bound: at center `b_1+b_2=min(a_c,a_{v_1}+a_{v_2})<=a_c`, and at leaf `i` the added coordinate is at most `a_{v_i}`. Decompose this vector into ordinary matchings, then forget the selected spoke edges. This yields a full heavy matching law `M` with each heavy marginal `x_h`.

Let `A` be the event that `c` is heavy-free, `A_1` that `v_1` is heavy-free, and `B` that at least one of `v_1,v_2` is heavy-free. A selected added spoke certifies that its endpoints are heavy-free. Since `Pr(A)=a_c`, `Pr(A_1)=a_{v_1}`, and a joint event cannot exceed the lesser marginal, `Pr(A∩A_1)=b_1=min(a_c,a_{v_1})`: the events `A,A_1` are nested. Similarly `Pr(A∩B)>=b_1+b_2=min(a_c,a_{v_1}+a_{v_2})`. If `a_c<=a_{v_1}+a_{v_2}`, this equals `Pr(A)`, so `A subseteq B` almost surely. If `a_c>=a_{v_1}+a_{v_2}`, the union bound gives `Pr(B)<=a_{v_1}+a_{v_2}=b_1+b_2`, so `B subseteq A` almost surely. Thus `A,B` are nested. These statements are simultaneous for the **same** full heavy law.

## Two scalar gap bounds

For the one-leaf prefix, let `U,W` be the heavy loads at `c,v_1` in the full matching. They lie in `{0} union [1/2,1]`. Their positivity supports are nested by `A,A_1`. The scalar lemma in [bipartite_fluid_matching_heterogeneous_heavy_transfer.md](bipartite_fluid_matching_heterogeneous_heavy_transfer.md) gives

`C_1:=E min(1−U,1−W) >= F_1(D)−1/3`, where `F_1(D)=min(D_c,D_{v_1})`.  (1)

For the two-leaf prefix, let `X=1−W_c` be the center residual in the full matching and `Y=(1−W_{v_1})+(1−W_{v_2})` the **raw**, untruncated leaf residual total. Then `F_2(M)=min(X,Y)` and `F_2(D)=min(EX,EY)`. Put `Z=X−Y`. For arbitrary real `Z`,

`min(EX,EY)−E min(X,Y)=min(E Z_+,E Z_-)`.  (2)

If `A subseteq B`, whenever the center is free (`X=1`) at least one leaf is free (`Y>=1`), so `Z_+=0` there. When the center is covered, `X<=1/2`, hence `Z_+<=1/2` pointwise. Thus `E Z_+<=1/2`. If `B subseteq A`, then in each state `|Z|<=1`: when a leaf is free, the center is free, giving `X=1,Y in[1,2]`; when no leaf is free, both leaf residuals are at most `1/2`, giving `Y in[0,1]` while `X in[0,1]`. Equation (2) therefore gives

`C_2:=E min(X,Y) >= F_2(D)−1/2`.  (3)

No independence of vertex states is asserted; both gap bounds use the exact augmented-matching coupling above.

## Four-phase deletion

Condition on the full heavy matching `M`. Give the selected heavy edge at center `c`, if any, phase color `1`. Give the selected heavy edge at top leaf `v_1`, if any, the **same** color `1`. Give the selected edge at `v_2` color `2` unless it is already the center edge (then it retains color `1`). Give the selected edge at `v_3` color `3` unless it is already the center edge (then it retains color `1`). Every other selected heavy edge receives any one color, say `4`. These assignments are consistent: a selected matching has at most one edge at each vertex, and the star leaves lie on one bipartition shore, so their incident selected edges are distinct. Choose a uniform `T in {1,2,3,4}` and delete every selected heavy edge of color `T`. Every heavy edge is retained with conditional probability `3/4`, hence has final marginal `(3/4)x_h`.

Let `F_k^{new}` denote the conditional fluid optimum for a unit-profit prefix of the first `k` leaves after deletion, and let `F_k^0` be its optimum in the full matching. For `k=1`, color `1` deletes every selected heavy edge at both prefix endpoints, so this phase makes both vertices fully free; the other three phases leave the prefix endpoint states unchanged. Therefore

`E_T F_1^{new} = 1/4+(3/4)F_1^0`.  (4)

For `k=2`, color `1` deletes the center edge and top-leaf edge and hence gives prefix recourse one. Color `2` leaves the original center residual `X` unchanged and frees `v_2`, giving recourse `X`. (If the center edge itself joins `v_2`, it has color `1`; in that case the color-2 state still has `v_2` residual `X`, so the recourse is again `X`.) Colors `3,4` leave the center and both prefix leaves in their original states, giving `F_2^0=min(X,Y)`. Thus the exact conditional identity is

`E_T F_2^{new}=1/4+X/4+F_2^0/2`.  (5)

For `k>=3`, if the center heavy edge joins any prefix leaf, that leaf's residual equals the center residual after every phase, so the prefix recourse equals the center residual in every phase. Its expectation is `1/4+(3/4)D_c >=(3/4)F_k(D)`. Otherwise, the selected heavy edges at the first three leaves have distinct phase colors `1,2,3` (unless a leaf was originally unmatched, in which case it is free in every phase). Thus at least three phases leave a fully free prefix leaf; their recourse is at least the **original** center residual `X`. Conditional phase average is at least `(3/4)X`; averaging full matchings gives `(3/4)D_c >=(3/4)F_k(D)`.

For `k=1`, average (4) over the full law and use (1):

`E F_1^{new} >=1/4+(3/4)[F_1(D)−1/3]=(3/4)F_1(D)`.

For `k=2`, average (5), use `EX=D_c` and (3), then `F_2(D)<=D_c`:

`E F_2^{new} >=1/4+D_c/4+(F_2(D)−1/2)/2 =D_c/4+F_2(D)/2 >=(3/4)F_2(D)`.

The fractional-knapsack layer-cake identity for a fluid star is

`F_q(r)=integral_{lambda>=0} min(r_c,sum_{i:q_i>=lambda}r_{v_i}) d lambda`.

The threshold sets are the profit prefixes. Integrating all prefix inequalities gives `E F_q(r(M_new))>=(3/4)F_q(D)>=(3/4)q·y`. The construction may depend on `q` but always fixes the exact target heavy marginals. Support-function separation therefore yields a joint one-color law with exact fluid mean vector `(3/4)y` and heavy marginals `(3/4)x`. This proves the scoped single-star transfer.

## Limits

The proof uses the fluid support being exactly one star to order its leaves and to augment `x` by its first two spokes. It does not presently synchronize the full-law nested-event requirements or the phase colors across a **forest of stars with heavy centers** linked by heavy edges, nor cover arbitrary fluid forests. Fluid edges are divisible and uncapped; no physical integer-coloring claim follows without an additional rounding/repair transfer.
