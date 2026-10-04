# Nested matching lift sufficient for the unrestricted mixed 3/2 inclusion

**Status.** The conditional-projection theorem below is proved. Universal feasibility of its nested-state LP is **open**. Thus this note does not claim a new unrestricted 3/2 bound. Diagnostic LP tests found no failure, but are not proof. Discrete heavy edges have weights `w_e in (1/2,1]`; fluid edges have divisible nonnegative amounts and arbitrary graph support. Parallel types are permitted. The local hull is exactly heavy count at most one and weighted heavy load plus fluid degree at most one, at each vertex.

Fix a locally feasible point `(x,y)` and put `alpha=2/3`. A heavy matching `A` is a set of selected heavy edge *types*. Let `B⊆A` be a second matching interpreted as the heavy edges that block their endpoints with **unit** capacity. For a binary state `(A,B)`, a fluid vector `z` is feasible if `deg_v z <= 1-1_{v covered by B}` for every vertex.

## Conditional-projection theorem

Suppose there is a joint law of `(A,B,z)` satisfying:

1. `A` is a heavy matching and `B⊆A` in every state; `z` is feasible under the binary residual capacities `1-1_{v covered by B}`.
2. `Pr(e∈A)=alpha x_e` for every heavy type `e`.
3. For every full matching state `A` with positive probability and every `e∈A`, `Pr(e∈B | A)=w_e`.
4. `E z_f=alpha y_f` for every fluid edge `f`.

Then `(alpha x,alpha y)` belongs to the **actual weighted** global-pattern hull.

**Proof.** For each `A` of positive probability, set `u_f(A)=E[z_f | A]`. The conditional binary feasibility inequality gives

`deg_v u(A) <= E[1-1_{v covered by B} | A]`.

If `A` covers `v`, its unique selected heavy edge there is `e`, and condition 3 makes the right side `1-w_e`; if `A` leaves `v` unmatched, the right side is one. Thus `(A,u(A))` is an actual weighted feasible global pattern. Its heavy means are `alpha x` by condition 2, and its fluid means are `E u(A)=E z=alpha y` by the tower property. This proof preserves the fluid means **edge by edge**; no profit separation or Jensen inequality is needed. Equivalently, for every concave fluid-profit value `F_q`, conditional Jensen gives `F_q(1-w1_A)>=E[F_q(1-1_B)|A]`, but averaging the feasible flows is stronger. ∎

## Exact finite nested-state LP

Enumerate all heavy matchings `A` and their submatchings `B⊆A`. Introduce nonnegative state masses `lambda_{A,B}` and state-weighted fluid flows `z_{A,B,f}`. Universal feasibility of the following LP for every local `(x,y)` is a sufficient conjecture for the desired unrestricted mixed `3/2` bound:

`sum_{A,B} lambda_{A,B}=1`,

`sum_{A,B:e∈A} lambda_{A,B}=alpha x_e` for each heavy `e`,

`sum_{A,B} z_{A,B,f}=alpha y_f` for each fluid `f`,

`sum_{B⊆A}(1_{e∈B}-w_e) lambda_{A,B}=0` for every matching `A` and `e∈A`,

`sum_{f∋v} z_{A,B,f} <= (1-1_{v covered by B}) lambda_{A,B}` for every state and vertex,

`lambda,z>=0`.

The fourth family is the **full-state conditional thinning** condition; unconditional binary marginals `Pr(e∈B)=alpha w_e x_e` alone do not imply the conditional-projection theorem. If this LP is feasible, define `P_A=sum_B lambda_{A,B}` and `u_f(A)=sum_B z_{A,B,f}/P_A`; summing the fourth and fifth families verifies the proof above directly.

The motivation is the proved unit-heavy theorem: the vector `(w x,y)` satisfies ordinary fractional matching degree inequalities `sum_{heavy e∋v}w_e x_e+sum_{fluid f∋v}y_f<=1`, so its `2/3` scaling admits an ordinary unit-matching rounding. The nested LP asks whether that rounding can be chosen jointly with an actual heavy matching `A` and the conditional thinning rule. For intersecting heavy support (a star or triangle), the binary heavy-state law is fixed by its type marginals, which is why the known intersecting-support theorem can perform this lift. For arbitrary heavy support, the choice of joint law is the unresolved part.

## A fixed binary law need not lift

Take two **disjoint** heavy edges `e,f` with weights `w_e=3/5`, `w_f=4/5` and local heavy means `x_e=1`, `x_f=1/2`. The desired actual marginals are `Pr(e∈A)=2/3`, `Pr(f∈A)=1/3`. The binary unit marginals are `Pr(e∈B)=2/5`, `Pr(f∈B)=4/15`. Consider the valid binary matching law

`Pr(B={e,f})=4/15`, `Pr(B={e})=2/15`, `Pr(B=empty)=3/5`.

It has exactly those binary marginals, but it admits **no** nested lift satisfying the full-state conditional probabilities. Since this binary law never has `f` without `e`, any full state `A` containing `f` must also contain `e`: otherwise the required conditional probability `Pr(f∈B|A)=4/5>0` would produce forbidden state `B={f}`. Conditional on `A={e,f}`, every event `f∈B` implies `e∈B`; hence `Pr(e∈B|A={e,f})>=Pr(f∈B|A={e,f})=4/5`, contradicting the required value `w_e=3/5`. This only rejects a **preselected** binary law. A different binary law may satisfy the nested LP for the same local means.

## Diagnostics and limitation

The reproducible script `transfer_nested_matching_probe.py` solved this exact LP for 3,000 randomly generated local extreme optima on 4–6 vertices, seed `623400`, using heavy weights from `{0.50001,0.6,0.75,0.9,1}` and random arbitrary fluid supports. No failure occurred. A second 10,000-case stress test, seed `441219`, used 4, 6, or 8 vertices, all disjoint heavy pairs selected with local mean one, random weights from the same grid, arbitrary dense fluid supports, and a locally optimal fluid flow for each random density vector. Again no failure occurred. Both tests used floating-point SciPy/HiGHS and are **nonexhaustive**. They establish neither universal nested feasibility nor the unrestricted `3/2` theorem.

The live obstruction is a simultaneous law-selection problem: one must round the ordinary fractional unit vector `(w x,y)` while retaining an augmentable binary heavy matching law and the full-state conditional thinning identities. Ordinary matching-polytope feasibility of the binary marginals, by itself, is insufficient, as the exact two-edge example shows.
