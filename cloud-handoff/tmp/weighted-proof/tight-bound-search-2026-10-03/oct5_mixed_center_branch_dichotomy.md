# A load-half phase split for mixed-heavy branching

5 October 2026. Exact elementary extension of the common-U product-flow calculation, followed by a necessary interface for high-load stars. This is not a full mixed-heavy star theorem.

Under the categorical matching-guard model of `oct4_mixed_heavy_comonotone_degree2_transfer.txt`, let `s_v=Σ_{e∋v}y_e` be the **target fluid load**, which may be strictly below local residual allowance `D_v`. The common-U residual moment bound is `M_{uv}=E[R_uR_v]≥1/3`. The same explicit coordinate flow

`f_e=(2/3)y_e R_uR_v/M_{uv}`

has exact means `2y_e/3` and satisfies `f_e≤2y_e≤C_e`. At any vertex whose **target load** `s_v≤1/2`, its statewise load is at most

`Σ_{e∋v} f_e ≤ 2R_v Σ_{e∋v} y_e =2s_v R_v≤R_v`.

Therefore the pure common-U policy works for an arbitrary fluid graph, with parallel identities and arbitrary guard weights `[0,1]`, whenever every vertex has target fluid load at most `1/2`; no simple-degree restriction is needed. This follows from the same moment bound and does not require the local allowance `D_v≤1/2`. More generally, high-load vertices may still be covered by the sharper degree-two Jensen test from the original note.

For a single mixed-heavy guarded-center star, this resolves the branch when its whole-star target mass `S≤1/2`, because each leaf target load is at most `S`. If `S>1/2` and every center heavy type has weight at least `1/2`, write its original total presence `x_c` and weighted load `a_c`. Local feasibility gives `a_c≤1−S`, while `a_c≥x_c/2`; hence `x_c≤2(1−S)`. At scaled heavy marginals `2x/3`, the probability that the center is **fully heavy-free** obeys

`q_0=1−(2/3)x_c ≥ (4S−1)/3 ≥ 2S/3`.

Thus, above the half-load threshold, the fully free center states alone have enough *aggregate* unit capacity to carry the desired fluid total. This is not sufficient for exact marginals: the leaf guards must be coupled so that their available capped fluid opportunities align with those free-center states without excessive bunching. The conditional center construction in `oct5_unit_center_mixed_leaf_star_conditional_transfer.md` does this when the center guard is unit weight; a nonunit center has smaller `q_0` but positive residual capacity when occupied, so an analogous proof needs to charge those two effects together.
