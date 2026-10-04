# Checkpoint: global coupling and stronger exact pricing

The unrestricted goal remains open. The authoritative manuscript still has
`4/3 <= c_bip <= 81/50` and `3/2 <= c_general <= 1999/1000`.
Nothing below changes either interval. The manuscript and clean private
Lean repository were not edited in this research pass.

The preceding user-requested repository cleanup was completed and verified;
it was not mathematical progress on the tight-bound goal. This pass adds a
new structural lemma and resolves a previously unfinished finite-grid test.

## Bipartite structural result

`bipartite_rank_two_first_cg_three_quarters.md` proves that when every weight
exceeds `1/3`, `(3/4) P_local` belongs to the entire first
Chvatal--Gomory closure of the local configuration polytope. This includes
all integer-normal valid local inequalities rounded down once, including
signed normals (by downward closure).

The substantive low-profit lemma is: if a nonnegative integral profit
vector has maximum global pattern profit at most two, its local LP value
is at most `5/2`; if the global maximum is one, the local value is one.
The proof reduces the positive support to a double star and uses nested
heavy--small compatibility. The root read the full proof and checked the
central profit-two cases and the signed-normal argument.

This is NOT containment in the global hull. Higher-round/global cuts
remain. In particular, the narrower mixed half-row-sum blossom family
is incomplete even on the existing K4,4 example. The exact integer checker
`verify_bipartite_k44_blossom_incomplete.py` was independently run by the
root: all 312,500 row/subset choices hold at a point outside the global
hull. Its separating inequality is itself a first-round CG inequality
with different multipliers; do not confuse the two families.

## Exhaustive global-pattern oracle and finite search

`search_mixed_triangle_ring_persisted.py` replaces repeated global MILP
pricing by a direct integer oracle. It enumerates all 6,006 coordinatewise
maximal count patterns for the nine-vertex, three-mixed-heavy-triangle,
medium-ring template. Heavy choices have seven possibilities per triangle;
after fixing those, it enumerates every legal medium bundle count and
rejects nonmaximal patterns. Downward closure and nonnegative prices
justify discarding nonmaximal patterns. The resulting array is
`mixed_triangle_ring_maximal_patterns.npy`.

Every run compares this oracle with the original integer solver in thirty
random/tied directions. All comparisons agreed. A branch-and-cut master
optimizes local means and integer profits jointly; every candidate is
priced against the complete pattern array. Cuts persist in
`mixed_triangle_ring_cuts.json` and are valid independently of price grid.

Completed runs:

- `mixed_triangle_ring_grid8_result.json`: the previously unfinished
  free-heavy-split grid with per-type profits in `0..8` and global price
  cap at most eight closed at objective zero in 485.70 seconds. Gurobi
  status OPTIMAL, bound zero; final candidate fully repriced. Largest
  repriced ratio was `3/2`.
- `mixed_triangle_ring_cube2_result.json`: all per-type integer profits
  in `0..2`, with no artificial global-price cap, closed at objective
  zero in 3.04 seconds, again fully repriced.

These closures rely on floating-point MILP optimization; no independent
rational branch-and-bound certificate was produced. The global pricing
array and its dot products are integer exact. Neither grid closure is
an unrestricted theorem or a proof for all real profit directions.

The expanded `0..8` profit cube reached its 600-second limit normally.
Its log is `mixed_triangle_ring_cube8.log` and its result is
`mixed_triangle_ring_cube8_result.json`. Solver status is TIME_LIMIT;
the master upper bound is about `0.84484`, while the incumbent gap is
`1.1e-9`, within numerical tolerance of zero. The final configuration
price is exactly 24, equal to its chosen cap; its substantive ratio is
`3/2`. This wider cube remains unresolved. In particular the positive
MASTER UPPER bound is not a positive lower certificate.

Shell sessions 53979, 74597, and 45158 all returned exit code zero and
are terminal. No root computation remains running. All three agents
also reported no live diagnostic sessions. A future continuation may
reuse saved cuts, but should not describe the completed run as live.

## Corrected linked-star bridge

`physical_linked_tiny_stars_capacity_two_bridge.md` records the exact
source-list problem for the heavy-matching/tiny-star physical model.
Every shared source has N states, touches at most two star components,
and contributes a number in `[0,1]` at each. If the states of every
source can be permuted so every hub's summed shared loads have range
at most two, private source lists can be counter-sorted locally; the
mean-at-most-one chord bound then gives total overload at most `N/2`.
This would yield the integer `3/2+O(tau)` bound for arbitrary heavy links.
The simultaneous range-two lemma is unproved.

A stronger proposed maximum-load-at-most-two lemma is FALSE for given
histograms: N=5, a private list `(2,2,0,0,0)` and singleton list
`(1/5,1/5,1/5,1/5,1/5)` have mean total one but maximum `11/5` under
every permutation. This is realized by three unit-heavy uv edges and
tiny spokes uz,vz,wz of total weights 2,2,1. The overload is `12/5`,
still below `N/2`; it is not a counterexample to the desired theorem.

The shared-list question is multi-coordinate equitable partition of a
partition matroid. Berczi--Liu--Reis--Tarnawski (2026),
https://arxiv.org/html/2608.13983v1 , proves one-coordinate equitability
and a weaker one-basis matrix discrepancy guarantee. It does not prove
the simultaneous range-two statement. Its prefix counterexample is not
an obstruction to this no-prefix problem.

## Next constructive route

For arbitrary heavy support plus divisible fluid, the active agent has
derived a nested-matching sufficient formulation. Select a matching A
with heavy marginals `(2/3)x`. Conditional on its full state, select a
submatching B so each edge e of A survives with probability exactly
`w_e`. Assign fluid in the unit capacities remaining outside B. If its
unconditional fluid mean is `(2/3)y`, average the fluid conditional on A:
the average is feasible in capacities `1-w_e` at occupied endpoints.
This recovers an actual heavy-plus-fluid pattern law.

The missing part is jointly finding A, its conditional thinning B, and
the fluid allocation. An arbitrary prechosen unit-matching law need not
have such a lift. The full theorem, state LP, and exact two-disjoint-edge
nonlifting example are saved in
`transfer_nested_matching_sufficient_theorem.md`; the root read and
checked the conditional projection proof and nonlifting example.
There were 3,000 arbitrary-support and 10,000 saturated-pair diagnostic
LPs without a failure; these are nonexhaustive floating-point checks,
not a proof of universal feasibility.

The bipartite pairing direction is saved in
`bipartite_rank_two_pairing_rounding_route.md`. Keeping one third of local
compatible pair mass would provide the desired scalar saving at tight
vertices, but three-vertex path atoms also need global color decomposition.
Neither coherence nor that decomposition follows from the scalar budget.
Pure directed heavy-small cross-rejections strictly increase small weight,
so they cannot form a directed cycle. This does not imply perfection of
the actual conflict graph, which can omit edges of the abstract interval
comparability graph.

The unrestricted problem additionally includes intermediate weights and
uniform transfer to integer physical-edge colorings. Do not substitute
any restricted coupling lemma for those remaining requirements.
