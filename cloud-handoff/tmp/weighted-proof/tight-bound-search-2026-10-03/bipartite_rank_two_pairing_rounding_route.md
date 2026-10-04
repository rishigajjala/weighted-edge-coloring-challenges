# A pairing-saving formulation for the rank-two bipartite 4/3 question

This is a reduction of the *load calculation*, not a coloring theorem.
All weights exceed `1/3`; heavy means `>1/2`, small means `<=1/2`.

Let `x` belong to the exact local configuration polytope. At vertex
`v`, put `H_v=sum_heavy x_e`, `S_v=sum_small x_e`. An exact fractional
local packing can pair a mass `m_v` of heavy and compatible small
items, with

    H_v + (S_v-m_v)/2 <= 1.                         (1)

The rest of the small mass is paired with other small items. If one
ignores every heavy-small pair and instead treats each heavy edge as
one matching token and each small edge as half a matching token, the
vertex load is

    D_v = H_v + S_v/2 <= 1 + m_v/2 <= 3/2.          (2)

This is the familiar `3/2` obstruction to the naive bipartite
matching decomposition: the token vector need not be a fractional
matching. Suppose a *globally coherent* construction can retain
compatible heavy-small pairs of total incidence mass `r_v` at every
vertex. Accounting for one retained pair as one two-edge bin instead
of `3/2` separate matching tokens would lower the formal load to

    D'_v = H_v + S_v/2 - r_v/2.                    (3)

The quantitative target `r_v >= m_v/3` then gives

    D'_v <= 1 + (m_v-r_v)/2 <= 1 + m_v/3 <= 4/3. (4)

At a tight vertex with `H_v=S_v=m_v=1`, this demands a saving of
exactly `1/6` of a color per local unit, or retention of `1/3` of the
heavy-small pair mass. The `1/3` is a useful concrete target for an
alternating-path/cycle argument.

**What remains unproved.** A heavy-small pair across two bundles is
a length-two path atom on three original vertices. Inequality (4) is
only a scalar incidence-load condition; it does not imply that the
chosen path atoms and residual edge tokens admit a decomposition into
globally feasible color patterns. Even choosing `r_v` coherently is
nontrivial: a physical edge has to receive the same color at both
endpoints, while each local pairing is specified at only one endpoint.
Thus a proof needs both (i) a globally consistent selection of enough
compatible pairs and (ii) an integral/fractional color decomposition
of the resulting path atoms and residual tokens. Applying the
bipartite matching polytope directly to `D'_v` would be invalid.

One way to see the cycle issue: for a rational `x`, clear
denominators and choose local bins at each vertex. Split each original
vertex into one node per local bin, and connect the two bin nodes
assigned to each physical edge occurrence. The auxiliary graph is
bipartite with maximum degree two, hence consists of paths and even
cycles. A component must be monochromatic if every local pair is
retained. It can nevertheless visit *two bins of the same original
vertex*. On an original four-cycle, take two singleton bins at one
vertex and pair the two incident edges in one bin at each of the other
three vertices. The auxiliary graph is a path joining those two bins
of the first vertex; making the path monochromatic violates their
distinct-bin requirement. At least one local pair must be broken.
The forest proof never faces this return-to-a-vertex phenomenon.

Nested heavy-small compatibility may permit exchanges of pairings
along these degree-two components, but (1)--(4) by themselves give
neither a universal `4/3` rounding nor a counterexample. The exact
first-CG-closure result is recorded separately in
`bipartite_rank_two_first_cg_three_quarters.md`.

## An interval-order restriction on cross-conflicts

There is a structural advantage beyond the raw load calculation. For
any locally compatible heavy-small pair atom `i` with heavy weight
`h_i` and small weight `s_i`, associate the nonempty interval

    I_i = [s_i, 1-h_i].

The heavy item of atom `i` rejects the small item of atom `j` exactly
when `h_i+s_j>1`, equivalently `1-h_i<s_j`. Thus `I_i` lies strictly
to the left of `I_j`. In particular every directed cross-rejection
arc `i -> j` strictly increases the small weight and there can be no
directed cross-rejection cycle. If one draws an undirected edge for
either direction of cross-rejection, this abstract graph is the
comparability graph of the interval order defined by disjoint
intervals. It is therefore perfect.

This does **not** prove colorability of the path atoms. The *actual*
cross-conflict graph keeps an abstract edge only when the relevant
physical incidences meet, and deleting edges from a perfect graph
can create an odd hole. Thus the interval-order fact rules out a
*directed* cyclic chain of cross-rejections but not every undirected
odd-cycle obstruction. Atoms can also conflict through two heavy
incidences at a shared vertex, or through the requirement that each
underlying physical edge receive one color at both endpoints. A
promising alternating-cycle proof would need to use the strict weight
order together with geometry to repair these conflicts within the
one-third pairing-loss budget.

## Exact matroidal baseline when all H-S pairs fit

If every heavy-small pair is compatible, a feasible local set of
edge occurrences is characterized simply by `|I|<=2` and
`|I intersect H|<=1`. These are the independent sets of a laminar
matroid at that vertex. Take the direct sum of these matroids over
vertices on the left bipartition side, and likewise on the right.
A global color pattern is exactly a common independent set of the
two direct sums. The matroid-intersection polytope is integral and is
the intersection of their independence polytopes. Consequently the
exact local configuration intersection already equals the global
color-pattern hull in this all-compatible subclass, even on cyclic
multigraph supports. Threshold-forbidden heavy-small pairs are the
only source of nonmatroidal behavior in this rank-two comparison.

For repeatable edge types, use two labelled copies of each type as
the finite matroid ground set. A projected local demand vector has a
canonical symmetric lift assigning half its demand to each copy:
average any lift over the two-copy swap. The same symmetric lift works
at both endpoints. Thus intersection of the projected local hulls
agrees with the projection of the two matroid polytopes' intersection;
this avoids silently assuming projection commutes with intersection.

Equivalently, one may first decompose `x` into globally feasible
*relaxed* colors under these matroid constraints. Every violation of
the original weighted rule is then specifically an incompatible
heavy-small pair at a vertex. This gives a globally edge-consistent
starting point for a repair proof; the unresolved step is to repair
all such defects with at most one-third extra color mass.

## Exact matching baseline when all H-S pairs are forbidden

There is an equally simple exact case at the opposite compatibility
extreme. If every incident heavy-small pair is incompatible at every
vertex, the exact local hull reads

    H_v + S_v/2 <= 1.

For a local vector `x`, define `z_e=x_e` on heavy types and
`z_e=x_e/2` on small types. The displayed inequalities make `z` a
fractional matching of the underlying bipartite multigraph. Decompose
it into integral matchings. In each matching use one copy of each
selected heavy type and two copies of each selected small type.
Because a matching has only one selected type at any vertex, every
resulting color is feasible. Its average count vector is exactly
`x`. Therefore `P_loc=P_glob` also in this all-incompatible case.
Both extreme regimes are integral; nontrivial gaps require a vertex
where some, but not all, H-S pairs are compatible.
