# Exact histogram gluing across low-degeneracy heavy links

**Status: proved conditional integer extension; unrestricted link graph remains open.** Use the physical-edge model and notation of `physical_single_tiny_star_integer_transfer.md`: heavy weights exceed `1/2`, the heavy simple support is a matching, tiny weights are at most `τ<1/2`, the tiny simple support is a vertex-disjoint star forest, and every vertex has an actual `N`-bin packing. Form the **link multigraph** `L` whose vertices are the nontrivial tiny-star components and whose edges are heavy-support pairs joining vertices in two different components. Count parallel links separately. Heavy pairs with both endpoints in one tiny star are internal; pairs touching an outside vertex with no tiny edge are dangling and do not enter `L`.

If `L` is **2-degenerate as a multigraph**, then there is an integer colouring of all actual physical edges with

`χ'_w(G)≤ceil(3N/[2(1−τ)])`.                         (1)

If `L` is a forest, the same construction gives the sharper bipartite bound

`χ'_w(G)≤ceil(5N/[4(1−τ)])`                         (2)

whenever the combined heavy-plus-tiny support is bipartite. As before, the algorithms are polynomial given the local bin lists; finding minimum `N`-bin packings is not asserted polynomial. No claim here covers an arbitrary link graph.

## A star with up to two already-fixed source lists

Align the two endpoints of every heavy pair by physical heavy identity, exactly as in the one-star proof. The resulting full source list has `N` rows; each physical heavy edge occupies one row, and each tiny edge occupies one row of its leaf-end subset. A whole source list can be permuted without duplicating edges. The local hub's original bin histogram gives the mean inequality

`mean(T−H)≤0`,                                         (3)

where `T` sums all non-own leaf proposal loads and `H=X−Z_own∈[0,1]` if the hub's heavy partner is its own tiny leaf, or `H=X∈[0,1]` otherwise. Each singleton leaf list has values in `[0,1]`; each private heavy pair joining two leaves in this same star gives a group list in `[0,2]`. Internal/private groups are always free to permute when this star is processed. A link source fixed by a previously processed star touches exactly one vertex of the current star, hence is either its `H` source or one singleton leaf source.

Suppose at most two link sources are already fixed rowwise.

* If `H` is **free**, start `T` with the sum of the zero, one, or two already-fixed singleton leaf lists. This initial list has width at most two. Add each remaining free singleton or private-group list in descending order against the ascending current `T`; permute only the *new* list, carrying its full source states. Opposite sorting preserves width at most two. Finally permute the free `H` source list in the same order as `T`. The difference `D=T−H` has width at most two.
* If `H` is **fixed**, at most one already-fixed singleton leaf list remains, because there are at most two fixed links. Start `D` as `−H` plus that optional fixed leaf load. Its width is at most two. Add each remaining free singleton or private-group list in descending order against ascending current `D`, permuting only the new source list. Opposite sorting again keeps `width(D)≤2`. The fixed `H` list is never moved.

The width claim is elementary: for two ordered rows, one sorted summand increases by a value in `[0,2]` and the oppositely sorted added summand decreases by a value in `[0,2]`; their sum differs by at most two in either direction. The same-order final alignment in the first case subtracts an ordered list of width at most one from an ordered `T` of width at most two, again giving difference width at most two. From (3) and the finite chord inequality, every such star has total overload

`Σ_(j=1)^N(D_j)_+≤N/2`.                           (4)

Crucially, already-fixed source lists are never permuted. All choices made at this star therefore preserve the full `N`-row states fixed at earlier stars.

## Gluing in a degeneracy order

A 2-degenerate multigraph has an ordering in which each vertex has at most two earlier incident link edges; count parallel edges separately. Process tiny-star components in this order. At a star, its earlier links are the already-fixed full source lists. Apply the preceding construction, thereby assigning rows to every free source list incident to it, including links to later stars. When a later star is processed, it inherits those exact row assignments. Since a heavy source has only two endpoints, each link is finalized at its first processed component and is never changed afterward. Dangling and internal source lists are handled as free lists at their unique tiny-star component. Heavy pairs wholly outside the tiny support can be assigned to distinct normal rows independently.

The result is `N` simultaneous normal colours, each containing every physical heavy and proposed tiny edge in exactly one row and satisfying every tiny leaf. By (4), hub trimming removes tiny weight at most `(1/2+τ)N` **in each tiny star**. The removed stars are vertex-disjoint, so pack their residual edge sets separately by Next Fit and overlay their extra palettes. Each needs at most `ceil([(1/2+τ)N]/(1−τ))` extra colours. Together with the normal `N` colours this is (1), independent of the number of stars.

If the combined support is bipartite, no private two-leaf group exists. When `L` is a forest, choose a rooted order with at most **one** earlier link source per star. If that fixed source is a leaf singleton, start `T` with it and add other singleton lists by opposite sorting, so `width(T)≤1`, then align free `H` in the same order. If the fixed source is `H`, start `D=−H` and add all singleton lists by opposite sorting. Both cases give `width(D)≤1`, hence overload at most `N/4` per star. Trim and overlay the deleted-star palettes as before, proving (2).

## Boundary at higher link degeneracy

With three already-fixed singleton leaf lists, their rowwise sum can have width three before any free list is assigned. For example, three fixed `[0,1]` lists can put all their ones in the same rows. The local mean condition alone does not force a width-two starting list, and no free permutation can change those three lists. The 2-degenerate theorem therefore does **not** follow by the same induction for arbitrary link graphs. This is a limitation of the ordering argument, not a counterexample to the desired unrestricted uniform integer bound.
