# Why direct cyclic closure of the graded guarded path loses the 4/3 gap

**Independent lower-bound research note.** This is a barrier for specified
families, not an unrestricted bipartite upper bound.

## The balanced guarded cycle has ratio at most 4/3

Let the medium core be a cycle of any length, with exactly `d` physical
edges on every core bundle. Every medium edge has weight in `(1/3,1/2]`,
and the weights within a bundle may differ. At every core vertex attach
exactly `d` private-leaf guard edges, each of weight greater than `1/2`.
There is no assumption at all about guard-medium compatibility. (For the
bipartite problem, take an even cycle.) Then

    d+ceil(d/2) <= bp(G) <= chi'_w(G) <= 2d,

and hence `chi'_w(G)/bp(G) <= 4/3`.

Indeed, at any core vertex its `d` guards occupy distinct bins. Each
guard can hold at most one medium edge, and the vertex has `2d` medium
edges. At least `d` media remain outside the guard bins, and no bin
holds three media. This proves the local lower bound. For the global
upper bound, give the guards `d` colors, putting one guard from each
private bundle in every color. Give the core another `d` colors, putting
one physical edge from *each* core bundle in every color. A core-only
color presents exactly two medium edges at each vertex, which fit since
each weighs at most `1/2`. This physical coloring works even when all
core and guard weights vary independently.

Thus a cyclic twist in the compatible guard/core pairs, by itself,
cannot improve the `4/3` construction when all bundles have the path
family's balanced multiplicity. In particular, allowing the one wrap
vertex to have a guard that also fits its incoming edge does not help.

## Incoming-incompatible guards make the balanced cycle exact

Add the stronger hypothesis that at every core vertex every guard is
incompatible with every edge of its incoming core bundle. Choose a
globally lightest physical core edge, of weight `w`, and let `v` be its
child endpoint in the cyclic orientation. Since each guard `h` at `v`
rejects that edge, `h+w>1`. Every outgoing edge at `v` has weight at
least `w`, so every guard also rejects every outgoing edge. At `v`,
all `d` guards need their own bins and all `2d` medium edges need `d`
further bins. Therefore `bp(G)>=2d`; the coloring above gives

    bp(G)=chi'_w(G)=2d.

The argument permits heterogeneous physical weights even *within*
bundles. It explains the failure of closing the strictly decreasing
graded path: cyclic descent must break at a minimum, and under the
incoming-incompatibility condition the break raises the local bound
to the cost of the separate palettes.

## The equal-profit counting barrier extends to directed pseudoforests

The count argument in `bipartite_branched_guard_count_barrier.md` needs
only that each core vertex have at most one **incoming bundle**; it does
not need acyclicity. Thus it applies to an oriented pseudoforest made
of directed cycles with outward trees, with any physical multiplicities,
arbitrary private guard weights above `1/2`, and medium core weights in
`(1/3,1/2]`, provided each guard rejects all incoming medium edges.

For completeness, write `a_v,b_v,g_v` for the incoming medium count,
outgoing medium count, and guard count; let `T` be the total physical
edge count, `n` the number of core vertices, and `B=bp(G)`. At each
vertex the local bins imply

    2B >= 2g_v+a_v+(b_v-g_v)_+.

Summing, using `sum a_v=sum b_v`, and writing
`P=sum(b_v-g_v)_+`, `Q=sum(g_v-b_v)_+` gives

    4Bn >= 3T + P+Q.                              (1)

For any feasible color, assign its guards to their core endpoints;
assign a singleton medium edge in a bundle to its child; and assign
two media in one bundle one to each endpoint. The assignment is
injective: one incoming bundle gives at most one assignment; an
outgoing assignment means two edges of weights above `1/3`, leaving
room for no other medium or guard; and a guard cannot coexist with an
incoming medium. Thus each color has at most `n` edges. Equation (1)
shows the equal-profit all-edge count certificate cannot exceed
`4B/3` on this larger family. This is **not** a coloring upper bound
for arbitrary multiplicities; unequal edge profits remain unaddressed.

## Finite LP diagnostic

`bipartite_cycle_guard_targeted.py` uses the existing full local
configuration-hull and repeatable global-pattern LP oracle. It checked
120 four- and six-cycle instances on capacity grid 60: rotating graded
medium weights, several guard-complement choices, and random mixed
complements. For each support it alternated nonnegative edge profits
and locally feasible demands from 14 starts. The saved log
`bipartite_cycle_guard_targeted.log` reports no candidate above `4/3`.
This finite, nonconvex search cannot establish a general upper bound.

To escape these barriers, a construction needs more than the direct
cycle closure: unequal multiplicities together with an unequal-profit
certificate, a core vertex with multiple incoming bundles, guards that
share nonprivate endpoints, or medium weights across another packing
threshold are possibilities. No improvement above `4/3` is claimed.
