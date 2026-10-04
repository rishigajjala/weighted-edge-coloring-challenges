# Independent audit: distinct-center capped hybrid bridge

4 October 2026. This audits `oct4_distinct_center_bridge_hybrid_capped.md` as revised after the cap-floor correction. **Verdict: no material gap found at its stated five-bundle, four unit-heavy-pair scope.** This is a support-function theorem for divisible fluid with conditional caps `C_e >= 12 y_e`; it is neither a general fluid-graph theorem nor an integer-coloring transfer.

## Statewise model and reduction to six rays

The two star groups use disjoint fluid vertices and can be taken together when both are available. Alternatively, one may take the bridge group. In each free/busy state this gives exactly the lower model

`I_B I_A u + I_C I_D v + I_B I_C (h-I_Au-I_Dv)_+`.

In particular, when both centers are free and only one outer pair is free, the formula chooses the better of the available star and bridge; when both outer pairs are free, it chooses the better of the sum of stars and bridge. It is therefore a valid recourse lower bound even when caps within a bundle are heterogeneous.

For `u>=v`, the break planes `h=v,u,u+v` produce the six rays listed in the source note. The model is linear within each cone. Scaling all profits in one bundle by a nonnegative scalar scales both its full-free optimum and that bundle's target profit. Thus the target upper bound used in the proof is linear on the same cones, and checking the six rays suffices. The `u<v` case follows by exchanging the two sides. If a bundle optimum is zero, every nonnegative-profit target on that bundle also has zero profit, so the scaling argument includes degenerate rays.

## Cap charges and local constraints

For a group with total target mass `s`, scaling its target by `k=min(12,1/s)` gives a feasible full-free capped flow: every edge respects `C_e>=12y_e`, and its center and leaf loads are at most `ks<=1`. Consequently its target profit is at most its full-free optimum times `max(s,1/12)`. This applies separately to the left spokes, right spokes, and bridge, including parallel identities. The rows `s_A<=min(b-r,2x)`, `s_D<=min(c-r,2d)`, `r<=min(b,c)` correctly account for the two leaves in each outer pair and the two center capacities. Maximizing `s_A+s_D+r` over these rows gives the displayed formula (4); the bridge initially uses spare capacity at both centers, then has zero net effect while displacing one spoke group, and finally decreases the sum when it displaces both.

The floor accounting is correct. On the OR ray, if either target group has mass at least `1/12`, at most one floor is charged, costing at most `1/18` after the `2/3` scale. If neither does, the scaled floored target is at most `1/9`. On the hard `(1,1,1)` ray, one non-small group leaves at most two floors, costing `1/9`; when all three groups are small, the scaled floored target is at most `1/6`. These are the precise charges needed; charging all floors unconditionally would be invalid.

## Event inequalities and algebra

The two-pair probability is `R(s,t)=(1+2 min(s,t))(1+max(s,t))/6`. Direct expansion confirms `R(s,t)>=(2/3)min(t,2s)` and `R(s,t)>=1/6` for allowances in `[0,1]`.

For the OR event, the independent and comonotone terms in the source note are exact. Truncating `a` at `b/2` and `c` at `b` preserves `min(b,2a+c)` and decreases the event probability. Its one-sided derivatives with respect to either outer allowance are at most `1/2`; therefore its margin over `(2/3)min(b,2a+c)` is minimized on `2a+c=b`. On that line the comonotone term is at least `p_a/4`. Independent symbolic expansion verifies the displayed quadratic `F(a,b)` and `4AC-B^2=4P(b)`. The certificate `P(b)>=15` yields the exact uniform margin `7/96`; equality occurs at `(a,b,c)=(3/8,1,1/4)`. The cap-floor charge `1/18` fits this margin, and the both-small case is covered by `H>=R(a,b)>=1/6`.

For the hard `(1,1,1)` ray, the statewise model is `I_A I_B+I_C I_D+I_B I_C I_{A\ busy} I_{D\ busy}`. The independent part of the last event is `(1+2b)(1+2c)(1-x)(1-d)/27`; its comonotone part is `[min(b,c)-max(x,d)]_+/6`. Lowering `x` to `b/2` or `d` to `c/2` preserves `g` and can only decrease the **whole statewise model**; the last event by itself need not be monotone. Identity (8), the residual decomposition after (8), and the lower bound `L(b,c)` follow by expansion. Independent symbolic checks reproduce both displayed formulas for `L-1/8`. The first case is decreasing in `b` up to `c/2`; the second displayed decomposition is termwise nonnegative. Thus `L>=1/8`, with equality at `(b,c)=(1/2,1)` and `(x,d)=(1/4,1/2)` (or the reflected parameters). This margin pays the two possible cap floors; the all-small case follows from `R(x,b)+R(d,c)>=1/3`.

The other four rays reduce exactly as stated: two pair events for the separate spoke rays, one pair event for the bridge ray, one OR event for `(1,0,1)`, and the sum of the two appropriate OR events for `(1,1,2)`. Each includes its own floor charge. Hence every nonnegative profit direction meets the `2/3` support bound, so the capped conditional recourse polytope contains the required marginal vector by separation.

Scope caveat: the argument relies on four disjoint *unit-heavy* pair sources, the specified five fluid bundles, and the common hybrid free-state law. No conclusion about arbitrary linked stars, weighted heavy types, or a physical finite-palette realization follows from this note alone.
