# An arbitrary-core counting barrier from guarded paired spokes

4 October 2026. Scratch-only **equal-fluid-profit support bound**, not a global convex-hull inclusion or an unrestricted weighted-edge-coloring theorem.

Take any finite graph of center vertices, with arbitrary divisible-fluid core edges joining centers. At each center `v`, add two private spoke leaves that are the endpoints of one unit-heavy matching pair; the center itself belongs to a different unit-heavy matching pair. The center's two spokes are uncapped fluid edges, each of unit profit, and each leaf has no other fluid edge. Heavy pairs may link two centers, but no spoke leaf is reused between stars. All core fluid edges also have unit profit. Let a locally feasible fluid target have spoke sum `s_v`, core incidence sum `t_v`, center-pair residual allowance `b_v`, and leaf-pair residual allowance `a_v`. Then

`s_v+t_v<=b_v`, `s_v<=2a_v`, and `b_v,a_v∈[0,1]`.

Under the fixed hybrid heavy law (probability `3/4` independent scaled pair-free indicators, `1/4` comonotone, each pair with allowance `D` free with probability `p_D=(1+2D)/3`), the probability that both the center and leaf pair of star `v` are free is

`R(a_v,b_v)=(1+2min(a_v,b_v))*(1+max(a_v,b_v))/6`.

In that event, take one full unit of either uncapped spoke; otherwise take none. These star choices are simultaneously feasible at all centers, regardless of core topology and correlations among heavy pair bits, because their physical vertices are disjoint. The expected number of fluid units in this one-color policy is `Σ_v R(a_v,b_v)`.

The key local inequality is

`R(a,b)>=(b+s)/3` whenever `s<=min(b,2a)`.                 (1)

If `a<=b/2`, direct algebra gives

`R(a,b)-(b+2a)/3=(1-b)(1-2a)/6>=0`.

If `a>=b/2`, the general pair bound `R(a,b)>=(2/3)min(b,2a)=2b/3` proves (1). Equality occurs in the sharp two-leaf-star limit `a=1/2,b=s=1`.

Sum (1) over centers. Every core edge is counted at both endpoints, so

`Σ_core y_e=(1/2)Σ_v t_v <=(1/2)Σ_v(b_v-s_v)`.

Therefore

`E[one-color fluid count] >=(1/3)Σ_v(b_v+s_v)
                         >=(2/3)(Σ_v s_v+Σ_core y_e)`.

This is a **network-size-independent barrier** to improving the general-graph `3/2` lower bound by attaching an arbitrary unweighted fluid core to these guarded paired-leaf stars and using only the all-fluid-edge-count price. The proof ignores core edges entirely in its selected one-color pattern; local spare center capacity pays their target count. It does not handle caps below one, reused spoke leaves, arbitrary unequal prices, or exact scaled marginals of individual fluid types. In particular, it does not settle the unrestricted bipartite `4/3` or general `3/2` gap.

There is a limited weighted version. Give the two spokes at center `v` arbitrary nonnegative profits and let `M_v` be their maximum. Suppose every core edge `uv` has profit `q_{uv}<=(M_u+M_v)/2`. The same one-color policy earns `Σ_v M_v R(a_v,b_v)` in expectation. The target spoke profit at `v` is at most `M_v s_v`, and the target core profit is at most

`(1/2)Σ_{uv}(M_u+M_v)y_{uv}=(1/2)Σ_v M_v t_v`.

Multiplying by `2/3`, using `t_v<=b_v-s_v`, and applying (1) after multiplying by `M_v` proves the same support inequality. This identifies the escape condition for an unequal-price lower certificate in this architecture: some core edges must be priced above the average of their endpoint spoke maxima, or another assumption (uncapped private spokes, one paired-leaf group per center) must fail. It is still one profit-cone theorem, not full hull inclusion.

Arbitrary nonnegative profits on the unit-heavy types may be added to this support comparison: the fixed heavy law realizes exactly `2/3` of each heavy target marginal, so their expected profit scales exactly and cancels from the inequality.
