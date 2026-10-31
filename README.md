# Weighted edge coloring

Lean definitions, theorem statements, and proofs for finite weighted graphs
and loopless multigraphs. Parallel edges have distinct indices, and every edge
has a weight in `(0, 1]`.

Authors:

- Rishikesh Gajjala, New York University Abu Dhabi
- Arindam Khan, Indian Institute of Science

## Entry points

- [Challenge.lean](Challenge.lean) collects the graph model, all definitions,
  and the five headline statements in one file that depends only on Mathlib.
- [Solutions.lean](Solutions.lean) proves all five statements in that
  exact model. Its conversion lemmas identify the parameters used by the
  proof library with those in the challenge file.
- [Verification.lean](Verification.lean) prints the public theorem types and
  their axiom dependencies.
- [WeightedEdgeColoring/](WeightedEdgeColoring/) contains the proof library.

The parameters are `deltaW` (maximum incident weight), `bp` (the least common
number of unit bins sufficient for every vertex star), and `chiW` (the least
number of feasible weighted edge colors). In a feasible coloring, the edges
of any one color have total weight at most one at each vertex.

## The five statements

| Problem | Graph class and bound | Formal proof in this repository |
| --- | --- | --- |
| 1 | Simple graphs: `chiW ≤ bp + o(bp)` | `solve_problem_1` |
| 2 | Bipartite multigraphs: `chiW ≤ 2 deltaW + o(deltaW)` | `solve_problem_2` |
| 3 | Bipartite multigraphs: `chiW ≤ (81/50) bp + o(bp)` | `solve_problem_3` |
| 4 | General multigraphs: `chiW ≤ 3 ⌈deltaW⌉` | `solve_problem_4` |
| 5 | General multigraphs: `chiW ≤ (1999/1000) bp + o(bp)` | `solve_problem_5` |

The five `solve_problem_*` theorems are in the namespace
`WeightedEdgeColoringChallenge`.

Every asymptotic statement uses a uniform epsilon-threshold formulation:
`∀ ε > 0, ∃ N ∈ ℕ, ∀ G` in the stated graph class, if the relevant parameter
is at least `N`, then `chiW ≤ (c + ε)` times that parameter. The threshold
is independent of graph order, parallel multiplicity, and the smallest
positive edge weight. The constants in Problems 3 and 5 are exactly
`81/50 = 1.62` and `1999/1000 = 1.999`. Problem 4 has no asymptotic error term.

For the unrestricted coefficient `1999/1000`, the library also provides
`WeightedEdgeColoring.subtwoBPAsymptotic_unrestricted` and the equivalent
additive formulation `WeightedEdgeColoring.subtwoBPAdditive_unrestricted` in
[SubtwoUnrestrictedProof.lean](WeightedEdgeColoring/SubtwoUnrestrictedProof.lean).

## Scope of verification

The formalization certifies the five stated existence bounds. These theorem
statements make no running-time claim for the coloring algorithms. The
manuscript provides the mathematical arguments and algorithmic constructions;
we do not claim that every intermediate lemma, lower-bound construction, or
running-time analysis has been formalized, or that the coloring algorithms
have been implemented end to end.

## Build and verify

The snapshot reviewed for the manuscript is revision
[`65856c8e27e4`](https://github.com/rishigajjala/weighted-edge-coloring-challenges/commit/65856c8e27e48efc51b429719e075f097a08e119).
The project pins Lean **4.27.0** and Mathlib revision
`a3a10db0e9d66acbebf76c5e6a135066525ac900`. Install Lean through
[elan](https://github.com/leanprover/elan), then run from this directory:

```bash
python3 scripts/check.py --fetch-cache
```

This downloads the pinned Mathlib cache, compiles all dependencies of
`Verification`, and checks the axiom dependencies of the five `solve_problem_*`
theorems and `WeightedEdgeColoring.subtwoBPAsymptotic_unrestricted`. The helper
runs at most three Lean processes at once; use `--jobs 1` for a sequential
build or `--jobs 4` for four processes. Fresh compiled files are reused on
later runs. Build outputs stay under the ignored `.lake` directory.

For the unrestricted theorem alone, after fetching the cache:

```bash
python3 scripts/check.py --module WeightedEdgeColoring.SubtwoUnrestrictedProof \
  --theorem WeightedEdgeColoring.subtwoBPAsymptotic_unrestricted
```

The standard Lake build is also supported:

```bash
lake exe cache get
lake build
lake env lean Verification.lean
```

The default Lake target includes all five solutions and their verification
module. Passing `--lake-build` to the helper uses Lake's normal scheduler
followed by the same axiom audit.

The proved statements use only Lean's standard axioms `propext`,
`Classical.choice`, and `Quot.sound`. The proof sources contain no `sorry`,
custom axiom declarations, or `native_decide` calls. Generated build files
and dependency caches are excluded from version control.
