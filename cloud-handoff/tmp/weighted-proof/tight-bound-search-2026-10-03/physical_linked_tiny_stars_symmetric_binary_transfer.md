# Arbitrary heavy links with symmetric binary shared source states

**Status: proved conditional physical integer theorem for a global
histogram class; the unrestricted weighted-vector case remains open.**
There is no bound on the number, degree, cycles, or parallel edges of
the tiny-star link graph.

Let `G` be a finite loopless weighted multigraph whose heavy physical
edges have weights greater than `1/2` and simple support a matching.
Every other physical edge has weight at most `tau<1/2`, and the simple
support of these tiny edges is a star forest. Let `N=bp(G)` and fix
actual feasible `N`-bin local packings, padded with empty bins. Align
the two endpoint bin lists of every heavy pair by the identity of the
physical heavy edge or `none`, as in the one-star transfer note.

At each tiny-star component, propose tiny edges from their leaf-end
local subsets. A heavy-pair source is **shared** if its two endpoints
belong to two different tiny-star components. For each aligned source
state, let `a` and `b` be its proposed contribution to the two star
hubs: the relevant leaf tiny-subset load, or the hub heavy load if the
heavy endpoint is a hub. Assume every state of every shared source
has contribution pair either `(1,1)` or `(0,0)`. Sources with only one
star endpoint, and sources with both endpoints in the same star, are
private and need no restriction beyond the original local packing.

Under this chosen-histogram condition,

`chi'_w(G) <= ceil[3N/(2(1-tau))]`.                       (1)

The bound colors every actual physical edge exactly once. It holds
uniformly in graph size and for arbitrary links among the tiny stars.
The condition is strong: a shared heavy pair joining a hub to a leaf
normally has asymmetric endpoint contributions and is not covered.

## Shared-source scheduling theorem

More abstractly, take any graph of star hubs. Each edge source `s`
between two hubs has a list of `N` states, each with vector `(1,1)`
or `(0,0)`. Several sources may join the same two hubs. If the total
number of active states incident to each hub is at most `N`, then
there are permutations of every source's `N` states into the `N`
rows such that the shared load lists at every hub have range width
at most two.

For each source `s`, let `m_s` be its number of `(1,1)` states.
Create a multigraph `H` on the hubs with `m_s` labelled parallel
unit edges for source `s`. Its maximum degree is at most `N` by
hypothesis. Also, for every pair `u,v`, its total multiplicity
`m(u,v)` is at most `N`, because it is part of each endpoint degree.
Apply the nearly equitable, edge-balanced `N`-edge-coloring theorem
of Shioura and Yagiura, [*A Fast Algorithm for Computing a Nearly Equitable Edge Coloring with Balanced Conditions*, Theorem 1](https://jgaa.info/index.php/jgaa/article/download/paper213/2762/2569).
It supplies an `N`-coloring of an arbitrary multigraph for which:

* incident edge counts in any two colors at a vertex differ by at
  most two; and
* between any fixed pair of vertices, edge counts in any two colors
  differ by at most one.

The second property and `m(u,v)<=N` imply that every color contains
at most one edge between `u` and `v`. Hence all active states of each
source receive distinct colors, even when several sources connect
the same pair of hubs. Assign the corresponding active full source
states to those colors, then assign its `N-m_s` zero states
bijectively to its remaining colors. Each source now has exactly one
full state per row, shared consistently at both endpoints. The
shared row load at a hub is exactly the degree of that vertex in the
corresponding color class of `H`, so the first property gives range
width at most two simultaneously at every hub.

## Private lists and physical transfer

For each tiny star, aggregate all sources private to that star by
successive opposite sorting of their full source-state lists. A
private heavy pair joining two leaves contributes a list in `[0,2]`;
every other private source contributes a list in `[0,1]`, including
a hub-to-own-leaf pair because its hub heavy load plus that leaf's
same-row tiny load is at most one. The opposite-sort width lemma
gives a private aggregate list of range width at most two. Match it
in opposite order against the already fixed shared aggregate list,
which also has width at most two. This permutes only private full
source states and yields proposed total hub loads of range width at
most two, without altering any other star's shared schedule.

The mean proposed hub load is the total physical incident weight
at that hub divided by `N`, at most one by its original local
packing. For a nonnegative list of mean at most one and range width
at most two, the finite chord inequality gives total overload at
most `N/2`; see Section 5 of
`physical_linked_tiny_stars_capacity_two_bridge.md` for its proof.
All tiny leaves remain feasible because their proposal in each row
is one actual local-bin subset with the same heavy identity. Trim
tiny physical edges at every overloaded hub, losing at most its
row overload plus `tau`; hence each tiny-star component has deleted
weight at most `N/2+tau N`. Next Fit packs the deleted edges of each
star into at most `ceil[(N/2+tau N)/(1-tau)]` extra colors. Overlay
these palettes across the disjoint stars, obtaining (1).

This proof uses the exact unweighted multigraph balancing theorem
only for the symmetric binary shared lists. Arbitrary physical
shared states may have unequal or fractional contributions at their
two stars; replacing them by unit edges would lose the load data.
Thus (1) is not an unrestricted heavy-linked-star-forest theorem.
