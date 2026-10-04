# Checkpoint: exact near-unit repair and the weighted potential obstruction

The full goal remains active and unsolved. Authoritative unrestricted
intervals remain `4/3 <= c_bip <= 81/50` and
`3/2 <= c_general <= 1999/1000`. No manuscript or Lean theorem was changed.
The user-requested repository cleanup is pushed at `15ad969`; research
files below remain outside the repository.

This research turn is **progress**: it proves new structural statements,
checks a restricted exact upper bound, and refutes a proposed general
proof method by an explicit construction. It does not close either
unrestricted interval.

## 1. Exact general mixed-model bound when heavy weights are at least 4/5

`transfer_near_unit_exact_three_halves_blossom_repair.md` proves the
coordinatewise `2/3` inclusion for arbitrary general heavy and divisible
fluid support, with heavy weights in `[4/5,1]`.

Treating all types as ordinary unit edges gives scaled vertex degrees
at most `4/5`. Only triangles can violate ordinary matching odd-set
constraints, and the violated triangles are vertex-disjoint. Remove each
triangle's excess from its fluid coordinates, decompose the resulting
point into ordinary matchings, and restore the removed fluid in states
where an internal heavy edge leaves sufficient residual capacity and the
third vertex is free. A crossing-edge charge proves that the available
mean restoration capacity pays the entire excess. The restoration
preserves every edge-type mean.

The parent independently checked the proof and corrected one equality
to an inequality in the shared-edge-triangle argument. This is an exact
mixed-model theorem, not an unrestricted physical-edge coloring theorem.

`transfer_direct_matching_bipartite_and_blossom_obstruction.md` also gives
a short exact `3/2` mixed-model bound for bipartite support with arbitrary
heavy weights above `1/2`, using the ordinary bipartite matching polytope.

## 2. The general mixed problem reduces to disjoint tight odd sets

`transfer_disjoint_tight_blossom_projection.md` proves the following for
all heavy weights above `1/2`. The scaled combined vector has strict
ordinary degree below one. Keep all scaled heavy coordinates fixed and
retain a maximum total amount of fluid inside the ordinary matching
polytope. Every removed fluid edge belongs to a tight odd set.

Maximal tight odd sets are vertex-disjoint: odd intersections uncross
to a tight union, while even intersections would force every degree in
the intersection to be one, contradicting strict degree slack. Every
matching in a decomposition has a near-perfect internal matching in
each such set.

This is the next substantive proof target: restore the removed fluid
inside one arbitrary odd set while preserving heavy marginals and
accounting for its possible crossing matching edge. Triangle restoration
is proved; larger odd sets and nested tight subsets remain open. Do not
replace this task with more numerical weight-cutoff tuning.

## 3. First rounded cuts: no lower weight restriction is needed

`unrestricted_first_integer_rounding_closure.md` proves, for the
repeatable edge-type local configuration polytope and arbitrary weights,

* `(2/3) P_local <= CG(P_local)` on all loopless multigraphs;
* `(3/4) P_local <= CG(P_local)` on bipartite multigraphs.

The earlier bipartite proof was restricted to weights above `1/3`.
For integral profit with local optimum below three, global optimum is
at most two, which itself forces every positive-profit type to exceed
`1/3` (otherwise three copies fit). Thus the restriction follows in the
only exceptional low-profit case. The general proof uses the analogous
star-or-triangle classification when global integer profit is one.

The extension was independently audited. First-round cut satisfaction
does not establish membership in the global hull, and nonrepeatable
physical-edge coordinates cannot use the same duplicate-type argument.

## 4. Binary source coupling is proved; weighted quadratic extension is false

`shared_source_range_two_audit.md` proves the source-permutation range-two
theorem for all asymmetric binary endpoint states, with arbitrary links.
A two-color signed alternating trail strictly decreases the integer
squared-load potential whenever a hub has gap at least three. This gives
a polynomial algorithm. Two independent audits checked the revisit and
root-return cases and the conditional physical tiny-star transfer.

The theorem extends to a common affine amplitude per hub, but not yet to
arbitrary real source states. A root construction disproves the suggested
weighted quadratic-minimizer extension:

`weighted_quadratic_balancing_counterexample.md` uses the 9-cube plus a
root. Port columns have entries `(5/1024,1)` and cube columns have
entries `(-1/9,-1/9)`. Every global minimum-norm signing has root
discrepancy `5/2`. Cube edge expansion gives the strict energy comparison
`4/81 > 25/512`. This is a short exact proof, not a solver certificate.
There is nevertheless an explicit alternative signing with maximum
discrepancy `2/9`, so range-two existence is not refuted.

Two agents independently checked this counterexample.
`verify_weighted_quadratic_counterexample.py` was run successfully with
exact Fraction arithmetic: 513 rows, 2816 columns, minimum energy `25/4`,
alternative energy `1024/81`, and positive comparison margin `23/41472`.
Do not try to prove the now-false weighted minimum-energy property.

## 5. New lower-bound diagnostic, with no improvement

`homogeneous_shore_higher_rank_polar.py` checks two mixed knapsack stars
against four homogeneous opposite stars, including weights below `1/3`.
For eight weight templates it enumerated all integer global patterns,
all numerical vertices of the global polar, and optimized the local
configuration LP in every resulting profit direction. Results are in
`homogeneous_shore_higher_rank_polar.jsonl`: 2323 polar vertices total;
largest numerical gap `31/28`, below the existing `4/3` lower bound.

This is numerical evidence for those eight templates only. It yielded
no new lower bound. The plain homogeneous-shore construction permits
`floor(1/w)` simultaneous copies of a type, so standard one-copy
assignment lower bounds do not directly transfer. Private guards leave
unguarded colors and do not enforce the missing one-copy constraint.

Root shell session 9656 returned exit code zero; all eight cases finished.
No root computation remains running. The binary-coupling and lower-bound
agents concluded. The general-bound agent is saving its final notes.
