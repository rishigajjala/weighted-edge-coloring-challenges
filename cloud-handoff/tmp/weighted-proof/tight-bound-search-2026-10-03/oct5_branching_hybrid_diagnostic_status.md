# Fixed unit-guard hybrid diagnostic

5 October 2026. `oct4_branching_hybrid_global_lp_probe.py` enumerates all guard states and solves a single LP for simultaneous fluid marginal retention, with caps exactly 12y. It sampled 3,000 local extreme targets on random labelled trees, branching caterpillars, cubic graphs, and sparse general graphs with 8--14 vertices, random guard pairings, and residual allowances from {0,1/64,1/16,1/8,1/4,3/8,1/2,5/8,3/4,7/8,1}. No sampled target had retention below 2/3; the minimum was 2/3 up to floating point rounding.

The LP was separately checked against the exact paired-two-leaf-star formulas at total target t=1/2,3/4,1; results agreed to numerical precision. This is finite floating-point evidence, not a proof for arbitrary targets or graphs.

The unit-heavy scope audit `oct5_unit_heavy_scope_audit.md` explains why resolving this fixed-law diagnostic would still not by itself improve the already-established physical coloring bounds. The main research priority is mixed heavy weights and medium-size edge compatibility.
