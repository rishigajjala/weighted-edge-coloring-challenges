# Graded paths across rank changes: proved barrier and exact-template diagnostics

**Status.** Only the equal-bundle propositions below are proved. The
finite local/global gauges use floating-point polyhedral enumeration;
they are diagnostics and do not establish a universal bound for
unequal multiplicities.

## Equal multiplicities, arbitrary rank descent below one half

`balanced_graded_path_all_ranks_four_thirds.md` proves: if each core
bundle and each complementary private guard bundle has the same
physical multiplicity `d`, and the core weights strictly decrease
from `w_0<1/2`, then

    chi'_w(G) ≤ d+ceil(2d/k),
    bp(G) ≥ d+ceil(d/k),       k=floor(1/w_0)≥2,
    chi'_w(G)/bp(G) ≤ 4/3.

This is exact for finite `d` and includes arbitrary later transitions
through ranks three, four, and higher. The coloring groups `k`
ordinary bipartite core matchings per weighted color and uses `d`
guard-only colors. The local lower bound comes from the first
incoming core bundle and the incompatible next guard.

There is also a universal `2d` coloring of this balanced family,
without any bound on the core weights: alternate two `d`-color
palettes along the path, putting each nonterminal guard with its
outgoing core edge in the same palette, and put the terminal guard in
the opposite palette from its incoming core edge. If the first core
weight `w_0>1/2` and weights decrease, `bp≥2d` at the first internal
vertex, so `chi'_w(G)=bp(G)=2d`. Thus a rank-one-to-lower-rank
cascade with equal bundle multiplicities has no gap.

## Exact local cost when guards match outgoing demands

For nonuniform core multiplicities `d_i`, suppose each nonterminal
guard bundle has exactly `h_i=d_i` edges and weight `1−w_i`, with all
core weights below one half and strictly decreasing. Set
`k_i=floor(1/w_i)`. At each internal vertex `v_i`, the local bin
number is **exactly**

    d_i + ceil(d_{i−1}/k_{i−1}).

The guard bins reject every incoming core edge and are distinct;
pair each outgoing edge with one guard, then pack the incoming
bundle in `k_{i−1}`-tuples. The root needs `d_0` bins; a unit-guard
terminal needs `h_m+ceil(d_{m−1}/k_{m−1})`. The maximum of these
quantities is `bp(G)`. Reconciling each core bundle's dispersed use
at its tail and concentrated use at its head remains the global
problem; this formula alone does not prove 4/3.

## Two-core threshold classification

For a two-core path with first weight `a∈(1/3,1/2)` and second
weight `b∈(1/4,1/3)`, guards `1−a,1−b,1`, the only variable
middle-vertex count patterns are `(1,2)` if `a+2b≤1` and `(2,1)`
if `2a+b≤1`. Because `a>b`, this gives three open threshold cells.
`graded_2to3_threshold_cells_polar.py` enumerates the full global
one-color hull and all vertices of its nonnegative-profit polar,
then maximizes each profit over the vertex-local configuration LP.
The numerical gauges in the three cells are

    both mixed patterns feasible:        5/4,
    only (1,2) feasible:              5/4,
    neither mixed pattern feasible: 19/15.

The `19/15` direction has normalized nonnegative profit
`(q_a,q_b,q_H0,q_H1,q_H2)=(2/5,1/5,2/5,2/5,1/5)`, so the
rank-three core has positive price. For a two-core rank jump `2→k`
with `k=4,5,6`, the same numerical threshold-cell enumeration found
gauge `5/4` in every discovered cell. Rational LP certificates have
not been generated, and the lattice scan is not by itself a formal
proof that every high-rank threshold cell was sampled.

## Longer nonuniform cascade diagnostic

`graded_rank_transition_path_lp.py` enumerates 97 exact one-color
count patterns for weights `(.49,.33,.249)` and complementary guards,
then solves global/local covering LPs for selected nonuniform
demands. The largest selected-profile ratio was `5/4`. The
full-profit polar calculation in `graded_three_core_full_polar.py`
has 47 polar vertices and numerical gauge `19/15`; the displayed
maximizer prices the first two core ranks and no third core edge.

`graded_five_core_rank_cascade_lp.py` covers weights
`(.49,.42,.331,.249,.199)`, crossing ranks `2→2→3→4→5`, with
1,413 feasible one-color count patterns. Across twelve structured
core-demand profiles and guard demands drawn from zero, incoming,
and outgoing counts, the largest numerical LP ratio was `5/4`,
again supported on the early rank-two segment. The finite probes
do not rule out a longer or more irregular demand profile.

## A real obstruction to the naive tripling proof

At a rank-two-to-rank-three transition, the feasible local bin
`.34+.34+.30=.98` tripled into canonical packets consists of two
rank-two doubles `.68`, two rank-two singletons `.34`, and one
rank-three triple `.90`. Exactly four bins force the two `.34`
singletons together, giving a paired same-bundle singleton state.
At the tail, each `.34` edge can be paired with its complementary
`.66` guard. Even allowing all three physical copies as singletons,
two such original guard/core bins repacked into at most eight bins
can pair at most two of the three possible singleton pairs, whereas
the head bin requires three. Therefore a straightforward canonical
`3G`-into-`4B` bundle-state gluing cannot handle this saturated
transition. The complete two-core physical configuration gauge is
only `5/4`, so this is a barrier to that proof template, not a
counterexample to the desired upper bound.
