# Independent heavy-pair sampling does not give two-thirds fluid recourse

Consider four vertices `u,v,c,c'`. The unit-weight heavy edges are `uv` and `cc'`; their simple support is a matching. The only fluid edges are `cu` and `cv`, and both have unit profit. Heavy presence at `uv` is `5/8`, heavy presence at `cc'` is `1/4`, and the fluid-load target is `y_cu=y_cv=3/8`. These data are locally feasible: each leaf has heavy load `5/8` plus fluid load `3/8`, while the center has heavy load `1/4` plus total fluid load `3/4`. The leaf laws can place their fluid on the complement of `uv`, and the center law can place total fluid `3/4` on the complement of `cc'`. Thus these are genuine one-vertex bin laws (with divisible fluid), not merely degree inequalities.

Scale every edge marginal by `alpha=2/3`, and independently select each heavy pair's state with its scaled presence. The `uv` pair is free with probability `1-(2/3)(5/8)=7/12`; the center `c` is free with probability `1-(2/3)(1/4)=5/6`. Both events are needed for any fluid edge. When both hold, the maximum total fluid profit is one because `c` has unit capacity. Hence the expected optimal fluid recourse is

`E F_q(R)=(7/12)(5/6)=35/72 < 1/2=(2/3)(3/8+3/8)`.

The proposed independent heavy-pair law therefore cannot realize the required scaled fluid marginals. This disproves the standalone inequality `E F_q(R) >= (2/3) F_q(D)` for paired Bernoulli capacities, even with unit heavy edges and a two-edge fluid star. It does **not** disprove the two-thirds convex-hull inclusion with correlated heavy states. For example, the scaled heavy probabilities are `5/12` and `1/6`; coupling the `cc'` heavy event as a subset of the `uv` heavy event makes the no-heavy probability `7/12`, enough to carry the required total fluid `1/2` (indeed each spoke may carry `3/7` when neither heavy is present).

The same obstruction is a one-parameter family. Set the leaf residual capacity `D_u=D_v=epsilon/2`, the center residual capacity `D_c=epsilon`, heavy presences `1-epsilon/2` and `1-epsilon`, and fluid loads `epsilon/2` on each spoke. For `1/2<epsilon<1`, independent scaled heavy states give availability probabilities `(1+epsilon)/3` and `(1+2epsilon)/3`, so

`(2/3) F_q(D)-E F_q(R) = (1-epsilon)(2 epsilon-1)/9 > 0`.

This also shows why a pair-by-pair conditional chord argument is insufficient: the center and leaf-pair availability events must be positively correlated in the tight recourse coupling.
