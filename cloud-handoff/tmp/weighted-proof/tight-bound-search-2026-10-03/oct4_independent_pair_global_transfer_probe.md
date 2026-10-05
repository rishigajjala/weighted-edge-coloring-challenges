# Independent pair activation: exact capped obstruction

4 October 2026. This question was already settled in `independent_heavy_recourse_counterexample.md` and `general_paired_activation_two_leaf_counterexample.md` without explicit small edge caps. The construction below makes the same obstruction satisfy **`C_e=12y_e<=1` for every fluid identity**. It disproves the proposed fixed independent-pair law, not the existence of a differently correlated two-thirds transfer.

Take four vertices `u,v,c,c'` with unit-heavy pairs `uv` and `cc'`. Put six parallel divisible-fluid identities on each of `cu` and `cv`, each with target `y_e=1/16`, cap `C_e=3/4=12y_e`, and profit one. Thus each spoke has target mass `3/8` and the center has target mass `3/4`. The original heavy marginals are `x_uv=5/8`, `x_cc'=1/4`.

These are genuine local one-vertex laws. At either leaf, the heavy edge occupies the vertex with probability `5/8`; in the complementary `3/8` state, place amount `1/6` on each of its six fluid identities. At the center, the heavy edge occupies it with probability `1/4`; in the complementary `3/4` state, place amount `1/12` on each of its twelve incident fluid identities. Each local bin has load one or less and each identity has expected amount `1/16`; the displayed conditional amounts are below its cap `3/4`. The unused vertex `c'` only sees its heavy edge.

At desired scale `alpha=2/3`, independently sample the two heavy pairs with probabilities `alpha x_uv=5/12` and `alpha x_cc'=1/6`. Their free probabilities are respectively `7/12` and `5/6`. All fluid profit requires both heavy pairs to be absent. Conditional on that event, the center has capacity one and the parallel caps allow it to fill one unit, so the optimal conditional fluid profit is **exactly one**. Therefore

`E F_q(R,C)=(7/12)(5/6)=35/72 < 36/72=(2/3) sum_e y_e`.

The deficit `1/72` is an exact support-function separation: no conditional fluid policy under this fixed independent heavy law can give every fluid identity marginal `2y_e/3`. The cap hypothesis cannot save the law; each cap is at the prescribed minimum and is at most one. Splitting a spoke into still more parallel identities makes every individual target and cap arbitrarily small while preserving the same obstruction.

More generally, give each spoke total target `t` with `1/4<t<1/2`, leaf-pair heavy marginal `1-t`, and center-pair heavy marginal `1-2t`. Split each spoke among sufficiently many parallel identities so that `C_e=12y_e<=1` and aggregate spoke cap is at least one. Then free probabilities under independent scaled guards are `(1+2t)/3` and `(1+4t)/3`, and the target-minus-recourse gap is

`(2/3)(2t) - [(1+2t)(1+4t)/9] = (1-2t)(4t-1)/9 > 0`.

This is only a method obstruction. For `t=3/8`, couple the scaled center-heavy event (probability `1/6`) as a subset of the scaled leaf-pair-heavy event (probability `5/12`): the resulting common-free probability is `7/12`, enough to route total fluid target `1/2` while respecting all the parallel caps. The hybrid independent/comonotone law used elsewhere supplies precisely this sort of positive inter-pair correlation. Any general proof at factor `2/3` must permit such correlation, or use a different non-independent construction.
