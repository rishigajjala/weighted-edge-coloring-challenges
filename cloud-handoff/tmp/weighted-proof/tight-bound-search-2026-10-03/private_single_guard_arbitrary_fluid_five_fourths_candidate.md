# Interim 5/4 transfer candidate for private categorical heavy guards and arbitrary divisible fluid

**Status (2026-10-03, during the required five-hour research period):** self-contained candidate proof awaiting independent audit. It is a restricted divisible-fluid local-hull statement, not a bound for physical indivisible small edges or heavy edges linking two fluid vertices. Heterogeneous parallel heavy types on each private guard pair are allowed.

## Model and claimed scope

Let `H=(V,E_f)` be any finite loopless fluid multigraph, with arbitrary nonnegative fluid quantities and no per-edge supply cap in a one-color configuration. Each fluid vertex `v` has at most one private heavy guard **pair** to a distinct external vertex that has no fluid incident edges. A guard pair may carry arbitrarily many heterogeneous categorical heavy types `i`, of weights `w_{vi}∈[0,1]`; at most one type can be selected in one color. All guard pairs are disjoint. Let `x_{vi}≥0` be the type presences and `y_e≥0` the fluid amount. The exact local polytope is

`P_loc={ (x,y): Σ_i w_{vi}x_{vi}+Σ_{e∋v} y_e≤1, Σ_i x_{vi}≤1 for v∈V, x_{vi},y_e≥0 }`.

The candidate conclusion is that `(4/5)P_loc` lies in the convex hull of feasible one-color guard-plus-fluid configurations. No bipartiteness of `H` is used because fluid edges are divisible. Strict-heavy applications take `h_v>1/2`; the proof would allow all `h_v∈[0,1]`. The factor is sharp in the strict-heavy limit by `bipartite_mixed_fluid_sharpness_audit.md`.

## Extreme-point sparsity

Fix a vertex `(x,y)` of `P_loc`, and let `S={e:y_e>0}`. In each connected component `C` of the positive fluid support, at most one guard pair can have a nondeterministic categorical state. If it does, exactly two states have positive probabilities: either no guard versus one type, or one heavy type versus another.

To see this, let `C` have `n` vertices and `m` positive fluid edges. At `v`, let `s_v` be the number of positive heavy type variables and let `rho_v=1` when the categorical constraint `Σ_i x_{vi}=1` is tight, and zero otherwise. Among the `m+Σ_v s_v` positive variables, at most `n+Σ_v rho_v` capacity and categorical rows can be active. Extremality therefore requires

`Σ_{v∈C}(s_v-rho_v)≤n-m≤1`,

because every connected graph has `m≥n-1`. Every term on the left is nonnegative. A term zero means either no positive heavy type, or exactly one type with probability one. A term one means either one type with probability strictly between zero and one, or two types whose probabilities sum to one. This proves the assertion. If `C` contains an even cycle, an alternating-sign perturbation of its positive fluid edges alone contradicts extremality; thus the positive support is a tree or odd unicyclic component, though this finer fact is not needed below.

## One-random-capacity recourse bound

Fix any nonnegative profit vector `q` on the positive fluid edges and one component `C`. Set `D_v=1-Σ_i w_{vi}x_{vi}`. Let `F_C(r)` be the maximum `q`-profit of divisible fluid on `C` under vertex capacities `r`. By the sparsity claim, there is a full-marginal guard law in which all guard states in `C` are deterministic except perhaps one categorical pair at vertex `v`. Its residual capacity has two possible values `a,b∈[0,1]`, with probabilities `p,1-p` and mean `D_v`. All other residual capacities equal `D` deterministically.

The one-coordinate function `f(t)=F_C(D_{-v},r_v=t)` is monotone and `L`-Lipschitz with `L=max_{e∋v}q_e` (take `L=0` if no positive fluid edge meets `v`). Indeed, decreasing `v`'s capacity by `delta` can be enforced by removing at most `delta` total incident fluid, losing at most `L delta` profit. Also `L≤F_C(1)`, since the single edge attaining `L` can carry one unit when all vertices have capacity one.

Order the two residual values so `a≤b` and write `d=pa+(1-p)b`. The Jensen gap obeys

`f(d)-[p f(a)+(1-p)f(b)] ≤ p[f(d)-f(a)] ≤ p(1-p)(b-a)L ≤ F_C(1)/4`.

If no guard state is random, the gap is zero. Choose independent guard states across distinct fluid components; this is physically feasible because every guard pair is private. Fluid recourse decomposes over components, so the full-marginal heavy law `M_full` satisfies, for every `q≥0`,

`E F_q(R(M_full)) ≥ F_q(D)-F_q(1)/4`.

The law itself depends only on `x`, not on `q`; the recourse optimum depends on `q`.

## Mix with the empty-heavy state and separate

With probability `4/5`, sample the preceding full-marginal guard law; with probability `1/5`, select no guard. Every guard now has exact marginal `(4/5)x_v`. Its expected optimal fluid profit is at least

`(4/5)[F_q(D)-F_q(1)/4]+(1/5)F_q(1)=(4/5)F_q(D)≥(4/5)q·y`.

This holds for every `q≥0`. At the fixed guard marginals `(4/5)x`, the feasible set of **mean** fluid vectors is convex and downward closed; its support function in direction `q≥0` is the maximum, over guard laws with those marginals, of expected fluid recourse. Therefore the separating-hyperplane theorem gives a joint one-color law with guard marginals `(4/5)x` and fluid means at least `(4/5)y`; downward thinning makes the fluid means exact. The q-specific optimizing fluid/guard law need not be common across q because support-function separation supplies one law for the target vector.

Every local point is a convex combination of vertices of `P_loc`; apply the argument to each vertex and mix the resulting global laws. This proves the stated inclusion if the extreme-point and separation arguments withstand audit.

## Boundaries and open extension

The **private-pair** condition is essential to the componentwise sparsity and recourse decomposition. A heavy edge linking two fluid vertices couples their categorical states and may link two fluid components; the dimension count then no longer ensures just one random capacity per component. That case is not covered. The proof also does not transfer to indivisible physical fluid edges without a separate rounding argument.
