# Balanced graded paths cannot exceed 4/3 across rank changes

**Scope.** This is a proved upper bound for one explicit family of
weighted bipartite multigraphs, not an unrestricted upper bound. It
allows any finite number of rank changes along the decreasing core
weights; it assumes the same multiplicity on every core and guard
bundle.

Let `v_0--...--v_m` be a path. Every core bundle has `d` parallel
edges, and every `v_i` has `d` private-leaf guard edges. Let the core
weights satisfy

    0 < w_{m-1} < ... < w_1 < w_0 < 1/2,

and give guard bundle `H_i` weight `1-w_i` for `i<m`; the terminal
guard `H_m` may have weight one or any value greater than `1/2` that
rejects incoming core edges. These are physical edges. Write
`k=floor(1/w_0)≥2`; all core edges have weight at most `w_0≤1/k`.

**Claim.**

    chi'_w(G) ≤ d+ceil(2d/k),
    bp(G) ≥ d+ceil(d/k),
    chi'_w(G)/bp(G) ≤ 4/3.

For the first inequality, use `d` guard-only colors, putting one edge
from every private guard bundle into each. The core multigraph is a
bipartite path with maximum unweighted degree at most `2d`. Properly
edge-color it with at most `2d` ordinary matchings, then group up to
`k` matchings into each weighted color. Every vertex meets at most
`k` core edges in such a color, so their total weight is at most
`k*w_0≤1`. There are at most `ceil(2d/k)` core-only colors.

At `v_1` (or at the terminal vertex if `m=1`), the `d` guards all
require distinct bins because each weighs more than `1/2`. Every
incoming edge from the first core bundle has weight `w_0` and is
incompatible with these guards: `w_0+1-w_1>1` if `m≥2`; the terminal
guard rejects them by assumption if `m=1`. The `d` incoming core
edges thus require at least `ceil(d/k)` additional bins. This proves
the local lower bound, regardless of how outgoing edges are packed.

For the exact ratio, write `d=qk+r`, `0≤r<k`. The desired inequality

    3*(d+ceil(2d/k)) ≤ 4*(d+ceil(d/k))

reduces to

    (2-k)q + 3*ceil(2r/k) - 4*[r>0] ≤ r.

It is immediate for `r=0`. If `0<r≤k/2`, the left side is at most
`-1`; if `k/2<r<k`, it is at most `2≤r`. Hence the bound holds for
every finite `d`, not only asymptotically.

This generalizes the uniform-harmonic-class batch argument: a path
can start with rank two and descend through ranks three, four, and
beyond, but the simple separated-palette physical coloring still
costs at most four thirds of the local bin number. To escape this
barrier, at least one of equal core/guard multiplicities, the one-path
shape, or the first-bundle bottleneck must be changed. Unequal
bundle demands are not covered; for them the same separated-palette
calculation can be loose because it ignores core/guard co-packing.
