# Research checkpoint: physical-edge transfer

The unrestricted objective remains unresolved. The manuscript's established
intervals are `4/3 <= c_bip <= 81/50` and
`3/2 <= c_general <= 1999/1000`. None of this turn's results changes those
unrestricted intervals. No exploratory material was added to the private
Lean repository or manuscript.

## Main advance

`physical_heavy_matching_tiny_star_forest_transfer.md` proves a theorem
about actual physical edges, avoiding the earlier replacement by divisible
fluid. Heavy edges have weight greater than `1/2` and their simple support
is a matching; all other edges have weight at most `tau < 1/2` and their
simple support is a star forest. With `N` local bins, the fractional
weighted chromatic number is at most

`[(3/2 - tau)/(1 - 2 tau)] N`.

For bipartite combined support and `N >= 3`, the factor improves to

`1 + (1/e + tau)/(1 - 2 tau)`.

These bounds preserve the inclusion probability of each physical edge.
They use the exact local-bin laws conditional on the identity of the
heavy edge, whole-edge deletion at a hub, and a separate correction law
constructed by unbiased floating-variable rounding. Two agents checked
the source-state coupling and correction independently; the root also
read and checked the complete proof. Fractional coloring alone does not
give a uniform integer bound.

A deterministic histogram-permutation argument, written in
`physical_single_tiny_star_integer_transfer.md`, gives an integer bound
when all tiny edges form a single star: counter-sort each new leaf-group
list against the current total, then sort the resulting total in the same
order as the hub's remaining capacities. The total difference has range
at most two and nonpositive mean, so its positive part sums to at most
`N/2`. Greedy whole-edge deletion adds at most `tau N`. Next Fit packs
the deleted star in at most `ceil(W/(1-tau))` further colors. Thus the
integer bound is

`ceil(3N/[2(1-tau)])`.

In the bipartite case no heavy pair joins two tiny-star leaves. All
leaf-group lists have range at most one, so the same proof replaces
`N/2` by `N/4` and gives

`ceil(5N/[4(1-tau)])`.

This algorithm takes local packings as input; it does not compute the
optimal bin-packing number in polynomial time. The general leading
constant `3/2` is sharp in this restricted class by the triangle with a
unit-heavy bundle and two tiny spokes. The simultaneous integer
permutation problem for heavy pairs joining multiple tiny stars is not
solved.

## Negative evidence and other scoped findings

- `transfer_physical_tiny_fluid_barrier.md` gives a finite-stock example
  where replacing tiny edges by fluid inflates both local and global
  one-pattern profit optima by `3/2`, even as the tiny weight tends to
  zero. It does not refute coordinated whole-edge rounding; the positive
  transfer above uses the original local packing laws to avoid it.
- `forest_extension_reserved_double_stars.md` extends the divisible-fluid
  half-deficit result to double-stars whose hubs are fixed-capacity or
  share one residual source. Distinct random hub sources remain open.
- `transfer_all_heavy_extreme_support.md` identifies a sparse extreme-point
  support for the arbitrary-heavy-plus-fluid local LP: at most `2|S|`
  positive types induced by any vertex set, or `2|S|-2` in the bipartite
  case. A boundary-law-preserving insertion argument is still required.
- The shared-guard and cycle searches did not improve the bipartite lower
  bound. In particular the `7/6` diagnostic in
  `bipartite_shared_guard_k44_exact_gap.md` is below the known `4/3` and is
  not an improved lower bound.

## Completed numerical diagnostics

`primary_general_pair_fluid_search.py` checked 4,999 random scalar-profit
coupling LPs with three or four paired capacity sources. Its largest
normalized loss was approximately `0.1316666667`. This search was weak
near the conjectured worst cases.

`primary_vertex_deficit_search.py` checked 16,000 random minimax
vertex-deficit LPs with three to five pair sources, fractional two-point
laws, and extreme mean-feasible flow targets. Its largest optimal deficit
was `1/2`. These are finite numerical diagnostics, not a proof of the
arbitrary-graph coupling claim. Both runs completed normally; their JSON
files record their terminal state. No process remains to be waited on.

## Next substantive steps

1. Extend the integer histogram construction to arbitrary heavy links
   between tiny-star components, with a residual-load bound at every hub
   simultaneously and an error independent of graph order.
2. Resolve the paired-capacity half-deficit inequality for general fluid
   forests, beginning with two distinct random hub sources.
3. Handle intermediate edge sizes and interacting heavy bundles; without
   this, even a full tiny-edge transfer does not solve the unrestricted
   goal.

Do not relabel the restricted fractional or one-star integer results as
the requested unrestricted tight bounds.
