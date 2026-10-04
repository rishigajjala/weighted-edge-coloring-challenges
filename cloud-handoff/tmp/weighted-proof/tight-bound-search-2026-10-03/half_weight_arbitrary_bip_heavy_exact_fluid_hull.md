# Exact bipartite fluid hull when all categorical heavy weights are 1/2

**Status (2026-10-03, within the required five-hour exploration interval):** scoped exact argument; not a claim about strict-heavy weights, heterogeneous weights, capped/physical small edges, or unrestricted weighted edge coloring. This is a boundary case that may inform a two-level rounding argument.

Let the combined graph be bipartite, with arbitrary simple or parallel heavy support. Every categorical heavy edge has weight exactly `1/2`. A one-color heavy set is an ordinary matching. Fluid edges are uncapped and divisible. The local polytope is

`x_h,y_e>=0`, `Σ_{h∋v}x_h<=1`, and `(1/2)Σ_{h∋v}x_h+Σ_{e∋v}y_e<=1` at each vertex.

**Claim.** This local polytope is exactly the convex hull of feasible one-color mixed states, with no scaling loss.

For each fluid edge `e`, create two distinguishable half-unit copies `e^1,e^2`. Keep one copy of each heavy edge. Lift an arbitrary local point by assigning both fluid copies marginal `z_{e^1}=z_{e^2}=y_e`, while a heavy copy has marginal `z_h=x_h`. At each vertex the lifted inequalities are

`Σ_{h∋v} z_h<=1` and `Σ_{h∋v} z_h+Σ_{e^j∋v}z_{e^j}<=2`.

At a vertex on the left shore, the incident-copy ground set has a laminar matroid: the heavy subset has rank at most one, the whole incident set has rank at most two, and each singleton has rank at most one. Direct sum these matroids over all left vertices to form `M_L`. Do the same on the right to form `M_R`. The displayed inequalities plus nonnegativity describe the two respective laminar-matroid independence polytopes. The lifted vector lies in their intersection. The matroid-intersection polytope is integral (equivalently, the intersection of the two independence polytopes is the convex hull of common independent sets), so the lift is a convex combination of integral common independent sets.

In an integral common independent set, selected heavy edges have degree at most one. Give each selected fluid copy amount `1/2` on its underlying fluid edge. The total load at every vertex is half the total selected-copy count, hence at most one. If both copies of a fluid edge are selected, it simply receives one unit of divisible fluid. Thus each integral common independent set is an actual feasible one-color mixed state. Averaging reproduces every heavy `x_h` and fluid `y_e`.

This argument relies on the edge weight exactly `1/2`: one heavy edge consumes precisely one of two identical half-unit slots. At an intermediate common weight such as `3/4`, a heavy edge consumes three of four slots while remaining one categorical item; the required synchronized triple is not a laminar-matroid element. Indeed scale one is false at `3/4`: take an unheavy fluid-star center joined to three leaves, each leaf incident with a separate external `3/4` heavy guard of marginal `8/9`; assign fluid `1/3` on each spoke. The local loads are one at every star vertex. In any full-marginal heavy law, the expected number of guard-free leaves is `1/3`. A full matching state with no free leaf offers star recourse `3/4`, and any other state offers at most one. Hence expected recourse is at most `3/4+(1/4)(1/3)=5/6<1`.
