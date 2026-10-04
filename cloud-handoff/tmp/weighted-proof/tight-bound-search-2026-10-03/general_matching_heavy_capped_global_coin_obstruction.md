# Finite caps defeat the global empty/full coin in the general 2/3 proof

3 October 2026. This is an obstruction to a **proof mechanism**, not a counterexample to capped `2/3` one-color inclusion. It already occurs in a bipartite fluid star with matching heavy support. The existing uncapped general-graph proof in `general_matching_heavy_odd_cycle_reduction_candidate.md` first constructs an arbitrary full-heavy-marginal law, bounds its fluid recourse by an additive fraction of the empty-state recourse, then mixes it with one global empty-heavy coin of mass `1/3`. That additive step is false with physical-style caps `C_e=12y_e`.

Let `m>24`. Take a fluid star with center `c`, leaves `v_1,...,v_m`, and edge `e_i=cv_i` of unit profit. Give each leaf a distinct unit-weight heavy guard edge `h_i=v_i u_i`; the heavy simple support is a matching. Put local heavy presence `x_{h_i}=1−1/m`, fluid target `y_{e_i}=1/m`, and fluid cap `C_{e_i}=12/m<1`. The local load is exactly one at every leaf and the center, and the cap condition is exactly `C=12y`.

Under **every** law with the full heavy marginals `x`, leaf `v_i` is heavy-free with probability `1/m`. Its fluid edge can carry at most `12/m` in a free state and zero otherwise, so

`E F_q(R_full,C) <= Σ_i (12/m)·(1/m) = 12/m`.

The empty-heavy state has fluid-star recourse `F_q(1,C)=1`, because `m·12/m>=1`. Therefore the full-law/empty-law mixture at weights `2/3,1/3` has expected recourse at most `1/3+8/m<2/3` for `m>24`, whereas the scaled target has profit `(2/3)Σ_i y_i=2/3`. Equivalently, the capped analogue of the additive estimate `E F_q(R_full,C) >= q·y−F_q(1,C)/2` fails: its right side is `1/2` and its left side is at most `12/m`.

This target is already an extreme point of its fluid degree polytope at the fixed residual vector: the positive support is a star, every leaf equation fixes `y_i=1/m`, and the center equation is tight. Consequently, decomposing the target into forest extremes with temporary caps `12y^k` does not repair this particular full-law additive estimate.

This does **not** rule out a different law with scaled heavy marginals `(2/3)x`. Such a law can spread heavy-free leaves over many colors instead of making all guards absent in one global empty state. The example pinpoints the missing ingredient for a capped general-graph transfer: a correlated law must simultaneously spread sparse capped fluid opportunities and preserve the positive correlations demanded by odd-cycle/paired-guard configurations. Independent scaled heavy pairs are known to fail even with uncapped fluid (`independent_heavy_recourse_counterexample.md`).

## Minimal odd-core comparison: two unit guards

There is a simple capped `2/3` law for the two-spoke triangle core when its two heavy guards are unit weight. Let one guard cover both fluid leaves with local presence `x_L`, and a disjoint guard cover the center with local presence `x_C`. Let spoke targets be `y_1,y_2`, with `Y=y_1+y_2<=1−x_C` and each `y_i<=1−x_L`. Assume caps `C_i>=2y_i`. At scale `alpha=2/3`, couple the two guard-absence events comonotonically; their common-free probability is

`p=min(1−alpha x_L,1−alpha x_C)=1−alpha max(x_L,x_C)>=1/3`.

The local inequalities imply `alpha Y<=p`. If `x_C>=x_L`, use `Y<=1−x_C`. If `x_L>=x_C`, use `Y<=min(1,2(1−x_L))` and split at `x_L=1/2`; in each range the inequality is elementary. In each common-free state send the fixed amount `alpha y_i/p` on spoke `i`, and otherwise send zero. Its center total is at most one, and `alpha y_i/p<=2y_i<=C_i`. Thus every heavy and fluid marginal is exact. This small positive law repairs the independent-pair failure on the odd core, but it does not solve the interaction with arbitrarily many capped branches.
