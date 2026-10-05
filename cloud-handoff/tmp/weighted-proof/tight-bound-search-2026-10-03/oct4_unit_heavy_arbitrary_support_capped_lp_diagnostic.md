# Unit-heavy arbitrary-support capped LP diagnostic

4–5 October 2026. This is a numerical and exact-boundary diagnostic for the **abstract divisible-fluid one-color hull**, not a new physical unit-heavy coloring result. The latter has a manuscript harmonic-charge route already; the next research target is heterogeneous heavy weights.

The reproducible finite-state LP is `oct4_arbitrary_unit_heavy_capped_lp.py`. It enumerates every matching of the positive heavy support. For each matching `M`, it has probability `p_M` and expected conditional fluid amounts `z_{M,e}`. It maximizes a common `alpha∈[0,1]` subject to `Σ_M p_M=1`, `Σ_{M∋h}p_M=alpha*x_h`, vertex capacities `Σ_{e∋v}z_{M,e}≤p_M` if `v` is uncovered and zero if covered, caps `z_{M,e}≤K*y_e*p_M`, and fluid marginals `Σ_M z_{M,e}≥alpha*y_e`. Thus this LP optimizes over **all** heavy matching correlations and conditional divisible-fluid policies for the specified input. Inputs obey only local degree rows `sum_h x_h+sum_e y_e≤1`.

The tests used K=2,4,12, arbitrary residual allowances including `.001,.01,.05,.2,.4,.7,.95`, sparse LP-extreme and iteratively scaled nonextreme fluid vectors, and random heavy/fluid supports. In 300 bipartite 8-vertex instances (seed 4), the smallest solved alpha values were `0.6671114,0.8006405,0.9239298`, respectively, above the proposed `2/3,4/5,12/13`. In 200 general 6-vertex instances (seed 2), minima were `0.5334756,0.6155740,0.6807352`, above `1/2,4/7,12/19`; 10 solver statuses were infeasible despite the obvious alpha-zero feasible point and are treated as numerical failures, not counterexamples. In 250 general 8-vertex instances (seed 7), minima were `0.5130836,0.5885815,0.6525995`; 9 similarly ambiguous solver failures were excluded. Output JSONL files in this directory have the corresponding names `oct4_unit_heavy_bip_n8_lp.jsonl`, `oct4_unit_heavy_general_n6_lp.jsonl`, and `oct4_unit_heavy_general_n8_lp.jsonl`. These finite samples do not establish the conjecture.

The LP reproduces the exact general triangle boundary. Put heavy support on all three triangle edges with each `x=(1-s)/2`, and fluid on the same three pairs with each `y=s/2`, `C=K*s/2`. A nonempty heavy matching covers two vertices, so fluid flows only in the empty-heavy state, whose probability is fixed as `p_0=1−3alpha(1−s)/2`. Fluid caps require `p_0≥alpha/K`; vertex rows require `p_0≥alpha*s`. Hence the exact optimum is

`alpha_triangle(s,K)=min(1, 1/[3(1−s)/2+max(1/K,s)])`.

For `s→0+`, this tends to `1/(3/2+1/K)`. The LP agrees numerically for s=.001 at K=2,4,12: `0.500375281,0.571918788,0.632177853`. Odd cycles of lengths five and seven with the same symmetric recipe gave strictly larger optima for all tested s and K; e.g. at s=.001, K=2 they gave `0.571837026` and `0.600420294`.

The bipartite diffuse-star boundary uses one unguarded center, k fluid leaves with `y_i=1/k`, `C_i=K/k`, and a private unit-heavy guard at each leaf with `x_i=1−1/k`. If `A` is the count of heavy-free leaves, expected fluid throughput is at most `(K/k)E A=K(1−alpha+alpha/k)`. Retaining total fluid `alpha` requires

`alpha≤K/(K+1−K/k)→K/(K+1)`.

The finite-k LP can be tighter due to the center's unit capacity; for k=8 it returned `8/11≈.72727` at K=2 and `8/9≈.88889` at K=4, exactly the displayed upper values. This establishes the proposed bipartite factor as an asymptotic upper limit, independent of any fixed-law sampling scheme.

No searched instance violated either proposed factor. The diagnostic is complete at the unit-heavy scope and should not be read as progress on arbitrary heavy weights `w∈(1/2,1)`, where occupied vertices retain real residual capacity and the matching-state LP must include those residuals.
