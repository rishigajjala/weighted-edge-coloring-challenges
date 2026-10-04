# Interim gap: synchronizing heavy-center star phases across a fluid star forest

The single-star transfer in [bipartite_single_fluid_star_heterogeneous_heavy_transfer.md](bipartite_single_fluid_star_heterogeneous_heavy_transfer.md) and the heavy-free-center forest transfer in [bipartite_unheavy_center_star_forest_phase_transfer.md](bipartite_unheavy_center_star_forest_phase_transfer.md) do not immediately combine when multiple heavy-centered stars are linked by selected heavy edges.

For a fixed full heavy matching `M`, the single-star proof wants the center-heavy edge and the top-profit-leaf-heavy edge deleted in the same phase. The selected heavy matching together with the fluid edges to the top-profit leaf of each star is a union of alternating paths/cycles. Equality of deletion phases propagates along each such component. The same proof wants the heavy edges at the top two and top three leaves of a star to have distinct phases unless a center edge itself joins a prefix leaf. After contracting equality components, this becomes a quotient coloring problem. A selected heavy edge can link different stars and propagate an equality across them. The quotient need not retain the original maximum-degree-three structure of the heavy-free-center case.

There is an explicit self-conflict with two bipartite fluid stars. Let star `S` have center `c_L` and right-shore leaves `a_R` (top one), `b_R` (top two). Let star `T` have center `x_L` and top-one right-shore leaf `y_R`. Choose three disjoint selected heavy edges `b_R x_L`, `y_R c_L`, and `a_R z_L`, where `z_L` is external. At `T`, equality of the center and top-one colors forces `color(bx)=color(yc)`. At `S`, it forces `color(yc)=color(az)`. Thus the heavy edges at `S`'s top two leaves `a,b` receive the same color, contrary to the convenient distinct-phase condition. If these are deterministic heavy edges, the local fluid target is already physically feasible; this is only a counterexample to the **overstrong phase-coloring prescription**, not to the `3/4` local-hull statement.

A naive quantitative repair is also insufficient without exploiting the graph's exchange freedom. Suppose at a star the top-two leaf edges collide with the center/top-one phase. For original center residual `X` and original two-leaf prefix recourse `H=min(X,Y)`, the four-phase mean becomes `1/4+(3/4)H`, instead of the distinct-phase identity `1/4+X/4+H/2`; the loss is `(X−H)/4`. This loss occurs only if center and both leaves have selected heavy edges, but the nested free-event scalar lemmas alone do not absorb it. An abstract full-state law illustrates the gap: with probability `4/5`, loads `(W_c,W_1,W_2)=(1/2,1,1)` and a collision; with probability `1/5`, loads `(1,0,0)`. Then the local residual means give `F_2(D)=2/5`, while the collision phase rule gives expected prefix recourse `1/4 <(3/4)(2/5)=3/10`. The full-law center-free probability is zero, so the nesting constraints are vacuous. This is **not** a constructed counterexample to the optimized heavy matching law: a graph realizing these marginals may allow an exchange to recouple the two leaf states.

The remaining proof target is either a joint heavy matching law and random phase deletion satisfying all star profit directions, or an exchange argument showing that every color collision is paid for by strict slack in the full-law scalar gap. A useful parity observation: the two top-leaf vertices of one star are on the same bipartition shore. If they are both selected only in one of two support matchings, their symmetric-difference components are distinct (an alternating path whose endpoint edges have the same color has odd length and therefore opposite-shore endpoints). Thus at least one leaf component can be swapped independently of a center component in the extreme anti-coupled pattern above. Turning this into a global quantitative bound is open in this note.

## Minimal forced-path collision family passes the target inequality

The self-conflict can be embedded in a heavy alternating path that **forces** a two-state full matching law. Let the heavy path be `b—x—y—c—a—z`, where `c` is the center of a fluid star with leaves `a` (top one) and `b` (top two). Put heavy marginal `p` on the three alternating edges of `M={(b,x),(y,c),(a,z)}` and `1−p` on the two alternate edges of `N={(x,y),(c,a)}`. Internal heavy vertex degrees are one, so every full-marginal matching state is `M` or `N` with probabilities `p,1−p`. The selected `M` edges fall in one equality component through the top-one fluid spokes of this and a second star, forcing the top-two collision. In `N`, the center heavy edge joins leaf `a`, which makes that star's prefix recourse equal its center residual.

Write `A=1−w_{yc}`, `B=1−w_{az}`, `C=1−w_{bx}`, and `E=1−w_{ca}`, all in `[0,1/2]`. The four-phase value at this star is

`V=1/4+(3/4)[p min(A,B+C)+(1−p)E]`.

Its local center and two-leaf residual totals are `D_c=pA+(1−p)E` and `D_l=p(B+C)+(1−p)(E+1)`. If `p<=2/3`, then

`V−(3/4)D_c >=1/4−(3/4)p(A−B−C)_+ >=1/4−(3/8)p >=0`.

If `p>=2/3` and `A<=B+C`, then `V=1/4+(3/4)D_c`, so `V` exceeds `(3/4)min(D_c,D_l)` by at least `1/4`. In the remaining case `A>B+C`,

`V−(3/4)D_l = (3/4)p−1/2 >=0`.

Therefore `V>=(3/4)min(D_c,D_l)` for every weight choice in the forced path family. This does not solve arbitrary star-forest synchronization, but it shows explicitly why the abstract collision-law failure above cannot simply be transplanted to the smallest forced matching support: its alternate state supplies the missing slack.
