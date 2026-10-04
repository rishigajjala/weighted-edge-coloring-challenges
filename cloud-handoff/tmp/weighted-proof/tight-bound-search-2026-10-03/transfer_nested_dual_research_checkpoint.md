# Nested matching LP: exact dual and current proof obstacle

**Status (2026-10-03).** The nested-lift sufficient theorem is proved in `transfer_nested_matching_sufficient_theorem.md`; universal feasibility and the unrestricted mixed `3/2` bound remain open. This checkpoint records only exact reductions and an unproved route. No counterexample was found. Research stopped on the parent task's request.

Let `alpha=2/3`. For a fluid nonnegative profit vector `q`, write
`F_q(r)=max{q·z:z>=0, deg_v z<=r_v for every v}`. For a heavy matching `A`, define

`Phi_q(A)=max_{law(B subset A): Pr(e in B)=w_e for every e in A} E_B F_q(1-1_{vertices covered by B})`.

The distribution is conditional on the *full* matching `A`. Its inner LP has one mass `lambda_B` for each `B subset A` and objective `sum_B lambda_B F_q(1-1_B)`. By LP duality,

`Phi_q(A)=min {t_0+sum_{e in A}w_e t_e : t_0+sum_{e in B}t_e >= F_q(1-1_B) for every B subset A}`,

where the `t` variables are unrestricted. For fixed local heavy marginals `x`, the largest achievable fluid profit under the nested LP is

`G_q(x)=max_{law(A): Pr(e in A)=alpha x_e} E_A Phi_q(A)`.

Its outer LP dual is

`G_q(x)=min {beta_0+sum_e alpha x_e beta_e : beta_0+sum_{e in A}beta_e >= Phi_q(A) for every heavy matching A}`,

with unrestricted `beta`. The nested LP is feasible for every locally feasible `(x,y)` if and only if, for every locally feasible `x` and `q>=0`,

`G_q(x) >= alpha F_q(1-Wx)`, where `(Wx)_v=sum_{e incident v}w_e x_e`.

The equivalence follows from convex separation: conditional fluid mean sets are compact, convex, and coordinatewise downclosed; local fluid demands at fixed `x` are exactly `deg y<=1-Wx`. Alternatively, without fixing `x`, the universal inclusion is equivalent to the scalar support inequality

`max_A [p(A)+Phi_q(A)] >= alpha max_{x,y local}[p·x+q·y]`

for all nonnegative heavy/fluid prices `p,q`. This has not been proved.

One possible sufficient route for *matching-supported fluid* would be to choose a liftable binary matching law `B` with prescribed marginals `Pr(e in B)=alpha w_e x_e` and enough pairwise unblocked probability. For a fluid edge `f=uv`, let `L_v=sum_{e incident v}w_e x_e`. To support the edge's target `alpha y_f` independently of other fluid edges, it suffices that

`Pr(u and v both unblocked by B) >= alpha min(1-L_u,1-L_v)`.

Writing `b_v=alpha L_v` and `I_uv=Pr(u and v both blocked)`, this is equivalent to

`I_uv >= alpha min(L_u,L_v)-1/3`.

The identity is exact, but existence of a **liftable** law meeting all these inequalities is unproved; and pairwise availability alone does not handle competing fluid edges at a vertex. For disjoint heavy support, a common-uniform activation for `A_e` and a second common-uniform conditional blocker coin give an illustrative pairwise construction, but no arbitrary-fluid feasibility proof was obtained.

The earlier 10,000-case diagnostic with all disjoint heavy pairs at local `x_e=1` is easy for a separate reason: when every fluid-incidence vertex lies in one of those pairs, take `A=all pairs` with probability `2/3`, `A=empty` with probability `1/3`, carry zero fluid in the first state and `2y` in the empty state. Since each covered vertex has `deg y<=1-w_e<1/2`, the empty-state flow is feasible. This explains why that stress family does not test the fractional-`x` obstruction. It does not extend when uncovered vertices can have `deg y>1/2`.
