# Arbitrary heavy support with a fluid matching: dimension-free 7/4 and a 3/2 coupling criterion

**Status.** The 7/4 theorem below is proved for any finite number of vertices. The final 3/2 criterion is an exact reduction, not a proof that its required matching law exists. Discrete edges have weights in `(1/2,1]`, so at most one can be selected at each vertex; fluid edges are divisible and their support is a matching. All profits and parallel heavy types are arbitrary and nonnegative.

Let `(x,y)` be a point of the full local configuration hull. Thus, at every vertex `v`,

`h_v := sum_{e heavy at v} x_e <= 1`,
`a_v := sum_{e heavy at v} w_e x_e`, and
`sum_{f fluid at v} y_f <= 1-a_v`.

For a fixed fluid profit-density vector `q`, put `F_q(r)=sum_{f=uv}q_f min(r_u,r_v)` and `A=F_q(1)=sum_f q_f`. The identity for `F_q` uses the matching support of fluid edges.

## Dimension-free 7/4 theorem

The vector `(2/3)x` lies in the matching polytope of heavy types. Its degree is at most `2/3`. For every odd vertex subset `S` of size `s>=3`, the degree bounds give `x(E[S])<=s/2`, hence

`(2/3)x(E[S])<=s/3<=(s-1)/2`.

These are all matching-polytope inequalities. Therefore some distribution on typed heavy matchings has heavy marginals `(2/3)x`. Sample one such matching `M` and let `R_v=1-w_e` if its selected heavy edge at `v` has type `e`, and `R_v=1` when unmatched. Then

`ER=(2/3)(1-a)+(1/3)1`.

For each fluid pair `uv`, the concavity gap of `min` for two random variables in `[0,1]` is at most `1/2`, irrespective of their joint law. Consequently

`E F_q(R) >= F_q(ER)-A/2 >= (2/3)F_q(1-a)-A/6`.

In this normal regime choose a fluid optimum under each realized `R`. Mix the normal regime with probability `6/7` and the fluid-only optimum with probability `1/7`. The heavy expected profit is `(4/7)p.x`. Fluid expected profit is at least

`(6/7)[(2/3)F_q(1-a)-A/6]+A/7=(4/7)F_q(1-a)`.

Since the locally feasible `y` has `q.y<=F_q(1-a)`, every nonnegative profit vector satisfies `C>=4L/7`. Thus the mixed local-to-global profit gap is at most `7/4`, independently of graph size. By support-function separation, `(4/7)(x,y)` belongs to the down-closed global pattern hull. The earlier five-vertex proof in `../all-heavy-plus-fluid-matching-seven-fourths.md` did not need its cardinality restriction; the only matching-polytope fact needed above holds for every odd set.

## Exact 3/2 matching-law criterion

Fix the local point `(x,y)`, and set `alpha=2/3`. There is a global distribution with heavy marginals `alpha x` and fluid means at least `alpha y` if and only if there is a distribution on heavy matchings with marginals `alpha x` such that, for every fluid pair `f=uv`,

`E min(A_u,A_v) >= alpha(a_u+a_v+y_f)-1`,                 (1)

where `A_v` is the realized selected-heavy weight at `v`, or zero if `v` is unmatched. Indeed, `R_v=1-A_v`, so

`E min(R_u,R_v)=1-alpha(a_u+a_v)+E min(A_u,A_v)`.

Fluid pairs are vertex-disjoint. If their expected residual-minimum capacities dominate `alpha y_f`, then in each heavy state put a constant fraction `alpha y_f / E min(R_u,R_v)` of the available `min(R_u,R_v)` on edge `f` (zero if the denominator is zero). This preserves the heavy law and reaches every fluid target; the converse follows from per-state capacity. Thus (1) is exact.

Because `y_f<=min(1-a_u,1-a_v)`, the right side of (1) is at most `(2/3)min(a_u,a_v)-1/3`. It is automatically nonpositive unless both mean heavy loads exceed `1/2`. This isolates the simultaneous heavy-occupancy correlation needed to improve 7/4 to 3/2. It is not supplied merely by choosing an arbitrary matching decomposition of `(2/3)x`.
