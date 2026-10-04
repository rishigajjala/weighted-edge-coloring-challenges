# Exact-stock empirical transport for arbitrary linked tiny stars

**Status: proved per-star expectation, not simultaneous integer colouring.** Retain the physical-edge heavy-matching/tiny-star-forest model and actual `N`-bin local histograms of `physical_single_tiny_star_integer_transfer.md`. Heavy pairs may link the tiny stars in arbitrary cycles. There is a random assignment of every physical edge to exactly one of `N` preliminary rows, with private leaf-pair rows optimally permuted within their own stars, such that **for every fixed star** its expected total hub overload is at most

`N/2+5 sqrt(N)`.                                         (1)

The expectation is over the common permutations of heavy-pair source lists and fixed-vertex lists. Formula (1) alone does not imply that one outcome satisfies this bound at all hubs independently of the number of stars. Consequently this note makes **no** arbitrary-star-forest integer-colouring claim.

## 1. Global shared permutations and private aggregate lists

Align the two endpoints of each heavy pair by its physical heavy identity, obtaining `N` full source-state rows. A source whose two endpoints are leaves of the **same** tiny star is private to that star. Every other heavy-pair source list, including hub-to-own-leaf and cross-star links, is given an independent uniformly random row permutation. Do the same for a fixed vertex's local-bin list when it is a tiny leaf. These permutations are global: a cross-star pair has one common permutation for both endpoint states, so every physical heavy edge and every leaf-proposed tiny edge still appears exactly once among the `N` rows.

Within one fixed tiny star, align its private two-leaf source lists by opposite sorting of their aggregate loads, carrying complete physical source states with the load values. The resulting private aggregate list `T_1,...,T_N` is deterministic after the private source lists are chosen, has its original total load, and has width at most two. It is independent of the random permutations of all nonprivate source lists. If there are no private sources, use the zero list.

In row `j`, let `U_j=1-X_j+Z_own,j+Σ_(singleton leaves a) Z_a,j`, omitting `Z_own` when the hub's heavy partner is not one of its tiny leaves. Every summand is in `[0,1]`, and the summand lists are independently uniformly permuted across **different** source pairs or fixed vertices. Thus each `U_j` has the same law `μ`, the law of a sum of independent `[0,1]` variables. The hub's local histogram gives

`E_μ U + mean(T)≤1`.                                     (2)

Each `U_j` is computed from complete shared source states, but only its load enters the next transport step.

## 2. Optimal finite matching against the private list

Let `ν=N^{-1}Σ_j δ_(T_j)` and `μ_N=N^{-1}Σ_j δ_(U_j)`. Define the one-dimensional transport value

`V(ρ,ν)=inf_{couplings (A,B) of ρ,ν} E(A+B−1)_+`.

Both `μ_N` and `ν` have `N` equiprobable labelled atoms. The transportation polytope is doubly stochastic, so a minimizing extreme point is a permutation: `N V(μ_N,ν)` is the minimum total preliminary overload obtained by permuting the complete private aggregate rows against the already assigned shared rows. Each such permutation preserves every private physical edge exactly once.

The independent-base/private-sum lemma from `upper_arbitrary_paired_star_forest_half_deficit.md` applies to `μ` and `ν`. Indeed `U` is a sum of independent `[0,1]` variables, `ν` has support width at most two, and (2) holds. Hence

`V(μ,ν)≤1/2`.                                           (3)

The value is one-Lipschitz in its first marginal for Wasserstein distance `W_1`: glue an optimal coupling of `(A,B)` to an optimal coupling of `(A,A')`, and use the hinge's one-Lipschitz dependence on `A`. Therefore

`V(μ_N,ν)≤1/2+W_1(μ_N,μ)`.                              (4)

Private source sets of different stars are disjoint, so their minimizing permutations can be chosen independently conditional on all globally assigned shared source rows. This gives one globally consistent `N`-row physical proposal assignment even when the heavy-link graph has cycles.

## 3. A dimension-free empirical `W_1` bound

The rows `U_j` are identically distributed but not independent: each source list is sampled without replacement by a random permutation. Nevertheless, for every threshold `t`, the indicators `I_j=1_{U_j>t}` have pairwise nonpositive covariance. Here is a direct proof. For two distinct rows of one source list, the two load values are drawn without replacement. If `f,g` are increasing functions of that scalar load, their covariance is `−Cov_emp(f(Z),g(Z))/(N−1)≤0`, since increasing functions of one scalar have nonnegative empirical covariance. Independent products of these two-row source pairs preserve this negative correlation for coordinatewise increasing functions: condition on all but one source pair, apply the one-pair inequality, and induct. The threshold indicators of the two row sums are coordinatewise increasing functions, so the claim follows.

Writing `p(t)=P_μ(U>t)`, we obtain

`Var[N^{-1}Σ_j I_j]≤p(t)(1−p(t))/N`.

Since `U≥0`, the one-dimensional survival-function identity and Jensen's inequality give

`E W_1(μ_N,μ) ≤ N^{-1/2}∫_0^∞ sqrt(p(t)(1−p(t)))dt`. (5)

The integral is bounded by an absolute constant. From (2), `E U≤1`; for independent summands in `[0,1]`, `E exp(λU)≤exp(e^λ−1)`. Chernoff with `λ=ln t` gives `p(t)≤exp(t−1−t ln t)≤exp(−t)` for `t≥8`. On `[0,8]`, `sqrt(p(1−p))≤1/2`, contributing at most four; on `[8,∞)`, it is at most `exp(−t/2)`, contributing `2e^{-4}<1`. Therefore

`E W_1(μ_N,μ)<5/sqrt(N)`.                        (6)

Combining (4) and (6) proves (1). The constant five is deliberately coarse and independent of the number of leaves, stars, heavy pairs, and physical edges.

## 4. Remaining simultaneous-permutation issue

The random global source permutations correlate the overloads of stars linked by heavy pairs. Equation (1) supplies a bound for each hub **in expectation** and therefore for any chosen weighted average of hub overloads, but it does not bound the maximum over arbitrarily many hubs in one realization. An ordinary union bound would introduce the number of stars. The manuscript's Harris--Srinivasan many-sums proposition applies to additive sums of *independent bounded choices* with bounded total contribution per choice; a whole source-list permutation is one choice that changes up to `N` rows, while the optimized overload is nonlinear in all shared permutations. Its hypotheses do not follow from (1). A dimension-free simultaneous selection theorem for these permutation/transport costs, or a counterexample, is still needed for the unrestricted linked-star integer transfer.
