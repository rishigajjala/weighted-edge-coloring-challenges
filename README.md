# Five weighted edge-coloring challenges

This private Lean 4 project collects five main weighted edge-coloring
problems in one self-contained file. The graph model allows parallel edges,
forbids loops, and gives every edge a weight in `(0, 1]`.

Authors:

- Rishikesh Gajjala, New York University Abu Dhabi
- Arindam Khan, Indian Institute of Science

## Start here

[`Challenge.lean`](Challenge.lean) contains every definition needed to read
the problems and the five formal statements. It depends only on Mathlib.

The three parameters are:

- `deltaW G`: maximum total incident weight at one vertex;
- `bp G`: minimum number of unit bins sufficient to pack every vertex star;
- `chiW G`: minimum number of feasible weighted edge colors.

A weighted edge coloring is feasible when the total weight of edges having
one color at any vertex is at most one.

## Problems

1. **Simple graphs:** `chiW G ≤ bp G + o(bp G)`.
2. **Bipartite multigraphs:** `chiW G ≤ 2 deltaW G + o(deltaW G)`.
3. **Bipartite multigraphs:** `chiW G ≤ (81/50) bp G + o(bp G)`.
4. **General loopless multigraphs:** `chiW G ≤ 3 ⌈deltaW G⌉`.
5. **General loopless multigraphs:**
   `chiW G ≤ (h∞ + 2/5) bp G + o(bp G)`.

The little-oh statements use uniform epsilon-threshold definitions. The
threshold can depend on the requested accuracy, but it cannot depend on the
number of vertices, the number of parallel edges, or the smallest edge
weight.

The file states each challenge as a named proposition. A solution can begin
without modifying the statement file:

```lean
import Challenge

open WeightedEdgeColoringChallenge

theorem solve_problem_1 : Problem1SimpleBP := by
  -- proof
```

## Check the project

```bash
lake update
lake exe cache get
lake build
```

The project is pinned to Lean 4.30.0 and a matching Mathlib revision.
