# A `4/5` transfer for one fluid edge and arbitrary bipartite heavy support

**Interim scoped result, independently audited in `one_fluid_edge_independent_audit.md`; the user's five-hour active exploration requirement remains in progress.** Let the combined support be bipartite. Heavy types have arbitrary weights in `[0,1]`, arbitrary bipartite support, and parallel types are allowed. There is exactly one uncapped divisible fluid edge `uv`. Then the full mixed local polytope scales into the one-color hull by `4/5`. For heavy weights in `[1/2,1]`, the constant is sharp as a limit by the paired four-vertex example in `bipartite_mixed_fluid_sharpness_audit.md`. This does **not** settle multiple interacting fluid edges, physical indivisible small edges, or uniform integer palettes.

The main lemma treats a heavy vector `x=p1_{M_0}+(1−p)1_{M_1}` for arbitrary `p∈[0,1]`, with `M_0,M_1` heavy matchings. Let `D_z=1−pW_z(M_0)−(1−p)W_z(M_1)` and `0<=y<=D:=min(D_u,D_v)`. We show `((4/5)x,(4/5)y)` is feasible.

Write `F(M)=min(1−W_u(M),1−W_v(M))`. First suppose `p=1/2`. The ordinary full-plus-empty scaled law has five equiprobable rows `M_0,M_0,M_1,M_1,empty`. Replace one triple `(M_0,M_1,empty)` by three matchings `C_1,C_2,C_3` obtained by properly edge-coloring the edge multiset `M_0⊎M_1` with three colors. One occurrence of an edge common to both matchings belongs to each of two colors. Every physical heavy type occurs twice across the final five rows, so its marginal is exactly `(4/5)x_h`. It remains to choose the coloring so that

`F(M_0)+F(M_1)+F(C_1)+F(C_2)+F(C_3) >= 4D`. (1)

If a selected heavy edge directly joins `u` and `v` in either full matching, no recoloring is needed. In each state containing that edge, the two fluid residuals are equal. With two full states, this makes `F(D)=[F(M_0)+F(M_1)]/2`: if the direct edge occurs in both, both states have equal endpoint residuals; if in just one, its common residual adds equally to the other state's two coordinates before taking their minimum. Thus the original five rows have fluid recourse `2F(M_0)+2F(M_1)+1>=4D`.

Assume now that neither full matching selects a direct `uv` heavy edge. Let `A_i=1−W_u(M_i)` and `B_i=1−W_v(M_i)` for `i=0,1`, with an unmatched endpoint assigned residual one. At each of `u,v`, the two incident edge *occurrences* in `M_0⊎M_1` can be given colors 1 and 2 so that the resulting residual pairs `(A_i,B_j)` are sorted together; color 3 is missing at both vertices. (If a vertex is unmatched in one full state, the missing occurrence can be assigned a notional color; this only fixes the other occurrence.) The prescribed local colors extend to a proper three-edge-coloring of the full multigraph `M_0⊎M_1`: each component is a path or an even cycle. If the marked vertices lie in distinct components, extend independently. If they lie in one component, every connecting path between `u` and `v` has odd length by bipartiteness. Length one would be a direct heavy edge, excluded here. On each path of odd length at least three, arbitrary prescribed colors on its first and last edges can be connected with three colors by assigning successive adjacent edges distinct colors. A cycle gives two such paths; dangling tails are colored greedily. Hence the coloring realizes the sorted pairing of the two endpoint residuals, and `F(C_1)+F(C_2)+F(C_3)=1+F_{sort}`, where `F_sort` is the sum of the two sorted pairwise minima.

Here is the scalar inequality. For arbitrary `A_0,A_1,B_0,B_1∈[0,1]`, put `F_orig=min(A_0,B_0)+min(A_1,B_1)` and let `F_sort` be the maximum over the two pairings. Then

`F_orig+F_sort+1 >= 2 min(A_0+A_1,B_0+B_1)`. (2)

To prove it, swap the endpoint labels if necessary so `S=A_0+A_1<=B_0+B_1`. Sort the numbers as `a<=A` and `b<=B`. For a pairing, its sum of minima is `S` minus the sum of positive deficits `(A_i−B_j)_+`. The sorted pairing minimizes this deficit; the crossed pairing maximizes it. Thus it suffices to show their two deficit sums total at most one. The crossed deficit is `(a−B)_++(A−b)_+=(A−b)_+`, since `a<=B` follows from `a+A<=b+B`. If `A<=b`, both deficits vanish. Otherwise:

- If `A>B`, then `a<b`, the sorted deficit is `A−B`, and the sum is `2A−b−B<=A−a<=1`.
- If `a>b`, then `A<=B`, the sorted deficit is `a−b`, and the sum is `A+a−2b<=B−b<=1`.
- In the remaining case, the sorted deficit is zero and the crossed deficit is at most one.

This proves (2). Since `D=min((A_0+A_1)/2,(B_0+B_1)/2)`, equation (2) is exactly (1). The five-row law therefore offers mean fluid recourse at least `(4/5)D>=(4/5)y`; thin the fluid amount in each row to achieve exact mean `(4/5)y`.

## Arbitrary probability on the same two-matching segment

For `p` arbitrary, let `F_i=F(M_i)` and `F_D=min(pA_0+(1−p)A_1,pB_0+(1−p)B_1)`. The full-plus-empty scaled law gives recourse `(4/5)[pF_0+(1−p)F_1]+1/5`. Define the two-state Jensen gap `C_p=F_D−[pF_0+(1−p)F_1]`. It suffices that `C_p<=1/4`. This automatically holds if `p<=1/4` or `p>=3/4`, since the elementary identity below gives `C_p<=min(p,1−p)`.

For `1/4<=p<=3/4`, the full-plus-empty law has at least `1/5` mass on each of `M_0,M_1,empty`. Replace exactly `1/5` mass of each by `1/5` mass on each of the three recolored matchings `C_1,C_2,C_3` above. This preserves every heavy marginal. Let `G=F_sort−F_0−F_1>=0`. The recourse gain from the exchange is `G/5`, so the desired scaled inequality reduces to

`1+G>=4 C_p`. (3)

If `Z_i=A_i−B_i` have the same sign, `C_p=0`; if a direct heavy `uv` edge appears, the earlier argument likewise gives `C_p=0`. Otherwise, after swapping state labels if necessary write `Z_0=d>0` and `Z_1=−e<0`, with `d,e∈[0,1]`. Direct calculation gives

`C_p=min(pd,(1−p)e) <= de/(d+e) <= (d+e)/4`. (4)

The sorted-pairing improvement obeys `G>=max(0,d+e−1)`. Indeed, the crossed original pairing has deficit distance `d+e` in the identity `min(a,b)=(a+b−|a−b|)/2`. The swapped pairing has distance `|A_0−B_1|+|A_1−B_0|`, which is at most `2−A_0−B_1+A_1+B_0=2−d−e` because `|s−t|<=2−s−t` and `|s−t|<=s+t` for `s,t∈[0,1]`. Its gain over the original is therefore at least `d+e−1`, and the optimal sorted pairing is no worse. Hence `1+G>=d+e>=4C_p`, proving (3). The resulting mean fluid recourse is at least `(4/5)F_D>=(4/5)y`.

## From one segment to the full one-fluid-edge local polytope

At any extreme point of the mixed local polytope with positive fluid coordinate, the extreme-face reduction in `arbitrary_heavy_bip_fluid_forest_extreme_face_reduction.md` shows that its heavy vector lies on a face of the bipartite matching polytope of dimension at most one. Thus it is an integral matching or a convex combination of two matching vertices `M_0,M_1`; the segment lemma above applies. At an extreme with zero fluid, simply decompose its heavy vector into matchings and then scale. Convexity of the target one-color hull extends the `4/5` inclusion to every local point with one fluid edge.

The proof uses opposite shores in the edge-color extension and bipartite matching-polytope integrality in the extreme-face reduction. The scalar inequality itself needs only residuals in `[0,1]`; the heavy lower bound `w_h>=1/2` is not used. Extending the five-state exchange to several interacting fluid edges remains open.

An **uncapped** fluid edge is essential. With one unit-weight heavy guard present with local probability `x=1/2` at one fluid endpoint, fluid target `y=1/2`, and a per-color fluid cap `C=1/2`, the local point is feasible. At scale `alpha`, the guard occupies probability `alpha/2`; in the other states fluid can supply at most `C=1/2`, so its mean is at most `(1−alpha/2)/2`. Requiring this to be at least `alpha y=alpha/2` forces `alpha<=2/3`. In particular the one-edge `4/5` result does not transfer to arbitrary capped or physical small-edge stocks.

For a single capped fluid edge, `C>=4y` is a simple sufficient condition for `4/5`: use a full-marginal H matching law with probability `4/5`, and the empty H matching with probability `1/5`; in the empty state route `4y` units of fluid. The assumption gives `4y<=C`, and since `C<=1` it also gives `4y<=1`. This factor four is asymptotically necessary for this empty-state-only construction, and indeed for the one-unit-guard example with guard marginal `x=1−y` as `y↓0`: at scale `4/5`, its free probability tends `1/5`, so achieving fluid mean `(4/5)y` requires cap at least `4y−o(y)`. This cap observation is separate from the uncapped theorem and does not handle several fluid edges sharing vertices.
