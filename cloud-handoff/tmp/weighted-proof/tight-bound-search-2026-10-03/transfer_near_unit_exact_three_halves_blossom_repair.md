# Exact 3/2 mixed-model inclusion for heavy weights at least 4/5

**Status: proved; independently audited by the parent agent.** Every discrete heavy edge has weight `w_e in [4/5,1]`; all other types are divisible nonnegative fluid. Heavy and fluid supports may be arbitrary loopless multigraphs with parallel types. The result is a coordinatewise inclusion of the `2/3`-scaled local configuration hull in the actual weighted global-pattern hull. It is **not** yet a result for arbitrary heavy weights `>1/2` or arbitrary finite stocks of small physical edges.

## Theorem

Let `(x,y)` satisfy, at every vertex `v`,

`h_v=sum_{heavy e incident v}x_e<=1`,

`sum_{heavy e incident v}w_e x_e + d_v<=1`, where `d_v=sum_{fluid f incident v}y_f`.

Then there is a probability distribution on actual mixed patterns `(A,u)`—`A` a heavy matching and `u` a divisible fluid flow with `deg_v u<=1-w_e` at vertices covered by `e in A`, and `deg_v u<=1` at vertices uncovered by `A`—whose means are exactly `E 1_{e in A}=(2/3)x_e` and `E u_f=(2/3)y_f` for every type.

## Step 1: ordinary unit matching vector and excess bound

Put `alpha=2/3`, `r_e=1-w_e<=1/5`, and regard every heavy and fluid type as an auxiliary **unit** edge. Its fractional vector is `z=(alpha x,alpha y)`. The local inequalities imply

`h_v+d_v <=1+sum_{heavy e incident v}r_e x_e <=1+(1/5)h_v<=6/5`.

Thus `deg_v z<=4/5` for every vertex. For an odd vertex set `S` of size `2k+1`, let `t_S` be the unscaled total heavy-plus-fluid mass on edges with both ends in `S`, `c_S` the corresponding unscaled crossing mass, and `R_S=sum_{v in S}sum_{heavy e incident v}r_e x_e`. Summing the preceding vertex inequalities gives `2t_S+c_S<=|S|+R_S`. The ordinary matching blossom excess is

`delta_S=alpha t_S-k <=[R_S-c_S-(k-1)]/3`.

Since `R_S<=|S|/5=(2k+1)/5<=k-1` for `k>=2`, every odd set of size at least five satisfies its ordinary matching blossom inequality. A violated blossom can only be a triangle.

Distinct violated triangles are vertex-disjoint. If triangles `T1,T2` share an edge `uv`, the sum of their two internal masses exceeds two, while that sum is **at most** `deg_z(u)+deg_z(v)` (other edges incident to `u,v` only increase the latter); hence `2<deg_z(u)+deg_z(v)<=8/5`, impossible. If they share exactly one vertex `v`, write one triangle's incident masses at `v` as `a,b` and its opposite edge mass as `c`. The other two vertices have degree at most `4/5`, so `a+c<=4/5`, `b+c<=4/5`; since `a+b+c>1`, these give `a+b>2/5`. Each violated triangle therefore uses more than `2/5` degree at `v`, so two such triangles would give `deg_z(v)>4/5`, impossible. These arguments use aggregate masses over parallel types.

## Step 2: remove the small triangle excess

For every violated triangle `T`, set `delta_T=z(E(T))-1>0`. Its **heavy** mass inside `T` is at most one: summing heavy-count rows over the three vertices gives `2 sum_{heavy e inside T}x_e<=3`, hence `alpha sum_{heavy e inside T}x_e<=1`. Therefore internal fluid mass is at least `delta_T`. Choose nonnegative amounts `d_f<=z_f` on fluid types inside `T` with `sum_{f inside T}d_f=delta_T`. Do this independently for the vertex-disjoint violated triangles, and reduce only these fluid coordinates to form `z'`.

The vector `z'` remains nonnegative, has vertex degrees at most one, and satisfies every odd-set inequality: sets of size at least five already did, the violated triangles are now tight, and no previously satisfied set can be worsened by coordinate decreases. By the ordinary matching-polytope theorem for loopless multigraphs, `z'` is the mean incidence vector of a distribution `mu` on ordinary unit matchings `M`. Its heavy means are still `alpha x`; its fluid means are `alpha y-d`.

For each repaired triangle `T`, `z'(E(T))=1`. Every ordinary matching contains at most one edge with both ends in `T`, so **every positive-probability matching in `mu` contains exactly one internal edge of `T`**. In particular, when that internal edge is a heavy edge `e`, its third triangle vertex `t` is the only vertex of `T` that might carry a crossing edge of `M`.

## Step 3: pay for excess fluid using heavy residual capacity

Call a matching state `M` **good for `T`** if its unique internal edge of `T` is heavy `e` and the third vertex `t` has no crossing edge of `M`. In such a state, the endpoints of `e` each have residual fluid capacity `r_e`, and `t` has capacity one. No other selected unit edge meets `T`. Consequently **any nonnegative internal fluid vector of total amount at most `r_e`** can be added at `T` without violating any vertex capacity: each triangle vertex sees at most that total. This remains true for parallel fluid types and for a fluid type parallel to `e`.

Define the mean available correction capacity

`K_T=E_mu[r_e 1_{M good for T and internal heavy edge e}]`,

where `r_e` is the residual of that state's selected heavy edge. Let `C_T=alpha c_T` be the mean number of unit matching edges crossing `T`, and `r_* =max_e r_e<=1/5`. Since a heavy-internal state can fail to be good only if `M` contains a crossing edge at the third vertex,

`K_T >= sum_{heavy e inside T}r_e z_e-r_* C_T`.                 (1)

The triangle excess bound gives a stronger comparison. Separate `R_T` into internal and crossing heavy contributions:

`R_T=2 sum_{heavy e inside T}r_e x_e+sum_{heavy g crossing T}r_g x_g`.

Therefore

`delta_T <=sum_{heavy e inside T}r_e z_e -(1/3)[sum_{heavy g crossing T}w_g x_g+sum_{fluid f crossing T}y_f]`.    (2)

Every crossing heavy has `w_g>=4/5>=2r_*`, and every crossing fluid has unit coefficient `1>=2r_*`. Thus the bracket divided by three is at least `(2/3)r_* c_T=r_* C_T`. Combining (1) and (2) proves `delta_T<=K_T`.

If `delta_T>0`, then `K_T>0`. In a good state with internal heavy edge `e`, add on every corrected fluid type `f inside T` the amount

`Delta_f(M)=d_f r_e/K_T`; add zero in other states. The total addition in that state is `delta_T r_e/K_T<=r_e`, so it is feasible. Its expected amount on type `f` is exactly `d_f`, by the definition of `K_T`. Perform these corrections simultaneously over all violated triangles. Their vertex sets are disjoint, so the statewise feasibility checks do not interfere. The resulting distribution on actual weighted mixed patterns has heavy means `alpha x` and fluid means `(alpha y-d)+d=alpha y` coordinatewise. This proves the theorem. ∎

## Scope and open extension

The proof uses `w_e>=4/5` twice: to eliminate every odd blossom of size at least five, and to force violated triangles to be vertex-disjoint through `deg_z(v)<=4/5`. The correction-capacity comparison itself only needs `w_min>=2/3`. Extending the exact `3/2` inclusion to all `w_e>1/2` requires a simultaneous repair of possibly overlapping triangles and larger odd blossoms; no such repair is claimed here.

For orientation below the threshold, if two violated triangles share exactly one vertex, their union is a violated five-vertex blossom: the two triangles have disjoint internal edge sets, so their combined internal mass exceeds two, whereas the ordinary matching bound for their five-vertex union is two. Hence triangle overlap naturally promotes to a larger odd blossom. This observation suggests a contraction hierarchy, but the proof above does **not** supply the necessary five-vertex correction transport.
