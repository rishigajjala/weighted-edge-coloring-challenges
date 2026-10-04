# Uniform integer transfer for one tiny star

**Status: proved, scoped integer theorem.** Let `G` be a finite loopless weighted multigraph. Its physical heavy edges have weights greater than `1/2` and simple support a matching. Every other physical edge has weight at most `τ`, where `0≤τ<1/2`, and the simple support of these tiny edges is **one star** (parallel edges allowed). Let `N=bp(G)`, the largest local unit-bin packing number. Then

`χ'_w(G) ≤ ceil(3N/[2(1−τ)])`.                         (1)

If the combined heavy-plus-tiny simple support is bipartite, then

`χ'_w(G) ≤ ceil(5N/[4(1−τ)])`.                         (2)

Both statements concern the actual physical edge occurrences: each is placed in one integer colour, without duplicate packet copies. The constants are independent of the number of vertices and edges. The leading coefficients tend to `3/2` and `5/4` as `τ↓0`. Given the local `N`-bin packings, the construction is polynomial in the listed physical input size: it aligns row lists by sorting, trims the hub, then runs Next Fit. No claim is made that minimum local bin packings can be found in polynomial time. This note proves the one-star case; it does **not** align `N` normal rows across several tiny stars linked by heavy pairs.

## 1. Exact `N`-row source lists

The edgeless case has `N=0` and is immediate. Assume `N≥1` below.

Fix an actual `N`-bin packing of the physical incident edges at every vertex, padding with empty bins. Because heavy simple support is a matching, each vertex has at most one heavy-support partner. For a heavy pair `uv`, label each of the `N` local bins at `u` and `v` by its heavy identity: a particular physical heavy edge on `uv`, or `none`. Every particular heavy identity occurs once at both endpoints, and `none` occurs the same `N−m` times, where `m` is the number of physical heavy edges on `uv`. Bijection-match the two endpoint bin lists within each identity. This gives `N` joint **full source states**, each with a common heavy identity and one actual tiny-edge subset at each endpoint. Each physical heavy edge occupies exactly one joint row. At each endpoint, each incident physical tiny edge occupies exactly one subset row in its local list; the proposal below uses only the leaf-end subset, so it never duplicates that edge. A vertex without a heavy partner has its own `N` local-bin list. Different source lists may be permuted freely; every permutation preserves these one-time occurrence properties.

Choose the tiny-star hub `o`. For every leaf `a`, propose the actual tiny edges in `a`'s subset in its source row. Let `Z_a` be their total weight. Local feasibility gives `0≤Z_a≤R_a≤1`, where `R_a` is the residual after that row's possible heavy edge. Only leaf subsets are used for proposals; the hub's original tiny subset is used later only through its total-weight inequality. A heavy pair with both endpoints outside the tiny star can be assigned injectively to the `N` normal colours independently, since its endpoints meet no tiny edge.

There are three types of source lists at the star:

* If a heavy pair joins two leaves `a,b`, its full joint source list contributes one **private group** `Y=Z_a+Z_b∈[0,2]`.
* If the hub's heavy partner is a leaf `a_*`, retain their joint full source list separately. Its row has hub residual `X` and own-partner tiny load `Z_*≤X`; put `H=X−Z_*∈[0,1]`.
* Every other leaf contributes one **singleton** load list `Z_a∈[0,1]`. If the hub's heavy partner is outside the tiny star, use the hub source list with `H=X`; if the hub has no heavy partner, use the constant list `H=1`.

No source list appears in two groups: the heavy support is a matching. The full source states, including physical heavy identities and tiny-edge subsets, remain attached to their load values throughout the permutations below.

## 2. Sort and align the finite lists

Let `T` be the rowwise sum of all private-group and singleton leaf loads, excluding `Z_*` if there is an own-partner leaf. Start with any one group list. Repeatedly sort the current aggregate `T` in ascending order, carrying its complete tuple of source states with each row, and match it against the next group load list in descending order, carrying that group's full source state. The new aggregate has range width at most two. Indeed, if the old aggregate and new group each have width at most two, then for rows `i<j` their increases in the first list and decreases in the second list are both in `[0,2]`; the difference of their summed values lies in `[-2,2]`. A singleton list has width at most one, and a private-group list has width at most two, so induction gives `width(T)≤2`. If there are no such groups, set `T=0`.

Now sort the aggregate `T` and the separate `H` list in the **same** order, permuting whole source states. Define `D=T−H` rowwise. Since `width(T)≤2` and `width(H)≤1`, two ordered rows differ in `D` by a number in `[-1,2]`; in particular `width(D)≤2`.

The mean of `D` is nonpositive. To see this, every proposed tiny physical edge appears once, so `Σ_rows(T+Z_*)` is exactly the total physical tiny-edge weight at the hub. In the hub's original `N` bins, tiny load in a bin is at most its heavy residual `X`; hence `Σ_rows(T+Z_*)≤Σ_rows X`, or `Σ_rows D≤0`. This argument is unaffected by the permutations.

For any finite list of width at most `L` and nonpositive mean, its average positive part is at most `L/4`. A proof is to place its values in `[a,b]` with `b−a≤L`: when `a<0<b`, the chord bound `d_+≤b(d−a)/(b−a)` gives average at most `b(−a)/(b−a)≤(b−a)/4`; the one-sided cases are immediate. Consequently,

`Σ_rows(D)_+ ≤ N/2`.                                  (3)

Each aligned row is an actual global proposal: it contains every heavy edge belonging to that row's source states and every proposed tiny edge from the aligned leaf states. Heavy edges do not conflict with one another because their simple support is a matching. Every tiny leaf respects its heavy residual by its own local row. Only the hub can be overloaded, and its overload is exactly `(D)_+`.

## 3. Trim and recolour actual residual edges

In each of the `N` proposed colours, delete tiny physical edges at the hub until the colour is feasible there. If its initial overload is `δ=(D)_+`, the total deleted weight is at most `δ+τ`: immediately before the last deletion it was still overloaded, and the last edge has weight at most `τ`. No leaf becomes infeasible by deletion. Therefore the total weight `W` of all deleted physical tiny edges is at most

`W≤N/2+τ N`.                                           (4)

All deleted edges lie in one tiny star. Pack them into new colours by ordinary Next Fit, treating the hub as one unit bin. Every closed bin has load **strictly greater** than `1−τ`. If `W>0` and Next Fit opens `q` bins, then `(q−1)(1−τ)<W`, so the integer `q` satisfies `q≤ceil(W/(1−τ))`; for `W=0`, use `q=0`. Hub feasibility implies feasibility at every leaf, since a leaf's selected tiny edges are a subset of the hub's selected tiny edges. By (4), the total number of colours is at most

`N+ceil([(1/2+τ)N]/(1−τ))=ceil(3N/[2(1−τ)])`,

proving (1).

## 4. Bipartite improvement

If the combined simple support is bipartite, no heavy pair can join two distinct leaves of the tiny star: that pair and their two spokes would make a triangle. Thus every group contributing to `T` is a singleton list of width at most one. The same opposite-sort induction gives `width(T)≤1`. Since `width(H)≤1`, same-order alignment gives `width(D)≤1`, and the finite chord bound improves (3) to `Σ(D)_+≤N/4`. Trimming deletes total weight at most `N/4+τ N`; Next Fit then uses at most `ceil([(1/4+τ)N]/(1−τ))` extra colours. Adding the normal `N` colours gives `ceil(5N/[4(1−τ)])`, proving (2). A heavy pair joining the hub to one leaf is permitted and is already absorbed into `H=X−Z_*`.

## 5. Scope and sharpness

For a disjoint union of tiny-star components with no heavy edge linking different components, the normal lists can be built independently and their colours overlaid; the deleted-star palettes can also be overlaid, giving the same bound with the global `N`. Heavy edges outside all tiny-star components can be overlaid on normal colours. A heavy pair joining two different tiny stars prevents independent row permutations, so this argument does not prove a forest-wide uniform integer theorem.

The `3/2` limit in (1) is sharp. For positive even `N`, integer `k≥3`, and `τ=1/k`, take `N/2` weight-one heavy edges on `uv` and `Nk/2` weight-`τ` tiny edges on each of `uz,vz`. The tiny support is one star, local packing needs exactly `N` bins, and the heavy edges need `N/2` colours disjoint from the `N` tiny colours forced at `z`. Thus `χ'_w=3N/2`. This triangle is outside the bipartite case.
