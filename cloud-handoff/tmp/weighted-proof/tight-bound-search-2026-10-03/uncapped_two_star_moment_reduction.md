# Uncapped two-star reciprocal inequality: exact reduction and moment data

**Status (2026-10-03): unresolved analytic inequality.** The cap-active probe and one-star cases are proved in `one_star_reciprocal_policy_lemma.md`. This note isolates the remaining uncapped, two-sided case and records numerical evidence only as evidence.

Fix target `y>0`, endpoint degree bounds `D_u,D_v<=1`, and independent vertex activations with `p_x=(1+3D_x)/4`. Let `K=4/3` and assume the probe is uncapped, so `b=Ky/(p_up_v)<=12y`, equivalent to `p_up_v>=1/9`. All other tentative coefficients may be increased to their uncapped values for a lower bound on the probe flow. Conditional on both probe endpoints active, let

`X = (K/p_u) sum_(i at u, i!=e) a_i B_i/r_i`,

`Y = (K/p_v) sum_(j at v, j!=e) a_j B_j/r_j`,

where `r_i` is the opposite-end activation probability. In a bipartite graph, the variables used in `X` lie on the right shore and those in `Y` on the left, hence `X,Y` are independent; parallel competitors sharing one opposite endpoint should first be aggregated. The rule's target is exactly

`E[1/max(1,b+X,b+Y)] >= 9/16`.

Put `s_u=D_u−y`, `s_v=D_v−y`. Padding each star's missing target load with a deterministic contribution if needed allows the relaxed means

`mu_u=K s_u/p_u`, `mu_v=K s_v/p_v`.

For one competitor target `a`, its minimum possible activation is `r(a)=(1+3a)/4`, and its variance contribution is at most `(K/p_u)^2 a h(a)`, where

`h(a)=3a(1−a)/(1+3a)`.

Since `h` increases on `[0,1/3]` and decreases thereafter, each star satisfies

`Var(X) <= (K/p_u)^2 s_u h(min(s_u,1/3))`,

and analogously for `Y`. Also each sum is nonnegative and at most `16/3`: `a/r_i<=4a`, so `X<=(4K/p_u)s_u<=4K=16/3` because `s_u<=D_u<=p_u`. The same holds for `Y`. Thus a stronger-looking but still open sufficient theorem is the identical reciprocal inequality for **arbitrary independent** nonnegative `X,Y` on `[0,16/3]` with these exact means and variance upper bounds. The actual star laws are a subset of this moment class.

Writing `U=1+3D_u`, `V=1+3D_v`, `W=1+3y`, the conditional mean load at `u` is at most `b+mu_u`, and its gap to the sharp value `16/9` is

`16/9−(b+mu_u) = 16[(W−2)^2+W(V−W)]/(9UV)`.

The analogous gap at `v` swaps `U,V`. This is the exact cross-compensation: extra competitor mass `D_v−y=(V−W)/3` at one side creates first-order mean slack at the *other* side. At the equality face `y=1/3`, `D_v=y`, the `u`-load mean can equal `16/9` while the `v`-competitor mass is zero. This explains why one-sided Jensen is sharp and why a two-sided proof must use the interaction between the two mean gaps and variances.

Numerical alternating linear programs over discretized moment laws (separate from exact star searches) have not found a ratio below `3/4`; a differential-evolution outer search converged to `y=D_v=1/3` and the one-star equality face. At `y→0`, `D_u=D_v=1`, the relaxed minimum ratio on a fine grid is about `0.7627`, only `0.0127` above target. These computations do not certify the continuous moment problem.
