# Why a common free prefix cannot prove the capped four-fifths transfer

**Status (2026-10-03): exact obstruction to one coupling strategy, not to the capped theorem.**

Consider a bipartite tiny star with an always-free center and `m` leaf heavy pairs. Each tiny spoke has target `y_i=1/m`; each leaf pair has target residual degree `D_i=1/m`, hence binary free marginal `p_i=1/5+(4/5m)`. The center target degree is one and its free marginal is one. Give every spoke cap `C_i=4y_i=4/m`. The desired four-fifths mean flow is `(4/5)y_i` per spoke, or `4/5` total at the center.

It is tempting to couple the mandatory `1/5` free probability of every leaf pair into one common event in which all pairs are free, then use the remaining `4/5` of colors with conditional free probability `1/m` per leaf. This cannot meet the target for large `m`. In the common event, the center carries at most one, contributing at most `1/5` to its expected flow. In the remaining phase, the expected number of free leaves is one, and each carries at most `4/m`, so its contribution is at most `(4/5)(4/m)=16/(5m)`. The combined upper bound is `1/5+16/(5m)<4/5` whenever `m>16/3`.

The obstruction is purely to **aligning** all leaves' baseline free states. A good coupling staggers those free states so about `m/5` leaves are free in each color. Then their combined cap is about `4/5`, matching the target, while every leaf retains its required free marginal. This also shows why a cap ratio below four cannot work asymptotically in this star: the total expected available capped flow is at most `K*(1/5+4/(5m))`, which tends to `K/5`, while the target is `4/5`.

The small exact-state LP searches in `paired_capped_45_lp_search.py` and `paired_categorical_capped_45_lp_search.py` allow arbitrary cross-pair correlations and have found no K=4 counterexample. They do not validate a common-free-prefix construction.
