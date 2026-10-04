# Three-item packet factors dilute the binary parity obstruction

4 October 2026. Scratch-only **equal-profit counting barrier**. This is not a coloring upper bound and does not exclude an unequal-profit gap.

Let `V` have even order `n`. Let the heavy support be the union of two perfect matchings `H_0,H_1`. Let the medium support be the union of two edge-disjoint `k`-regular spanning subgraphs `P_0,P_1` (`k=2` is the three-items-per-bin case). Every edge type has `N` physical copies. At each vertex suppose the incident heavy weights are `h_0,h_1` and the respective packet weights have sums `s_0,s_1`, and **both** proposed local bins `H_0+P_0` and `H_1+P_1` fit. The labels can vary with the vertex, but the two global heavy matchings and two global packet factors must each be chosen consistently. Suppose also the local bin-packing number is `2N` (as it is if all `2(k+1)N` incident edges are covered by these two bins and the heavy edges alone require `2N` bins).

Choose uniformly and independently one heavy matching and one packet factor, taking all their edge types in a one-color candidate. This selects `(k+1)n/2` edges. At a vertex, order the selected heavy weights as `h_L<=h_H` and the two packet sums as `s_L<=s_H`. The hypothesis that some pairing of the two heavies with the two packet factors fits implies `h_L+s_H<=1` and `h_H+s_L<=1` after relabeling (if the fitted pairing already matches the sorted orders, these inequalities still follow by monotonicity). In particular `h_L+s_L<=1`. **Only** `(h_H,s_H)` can be infeasible among the four choices. Its probability is at most `1/4`, even when the global phase choices correlate all vertices.

For every bad vertex delete its selected heavy edge. This repairs the whole packet there, cannot damage feasibility elsewhere, and deletes at most one edge per bad vertex. Some one-color set therefore contains at least

`(k+1)n/2-n/4=(2k+1)n/4`

physical edges. The graph has `(k+1)nN` physical edges in total. Thus an all-edge-count fractional lower certificate has ratio at most

`[(k+1)nN / ((2k+1)n/4)]/(2N)=2(k+1)/(2k+1)`.

For `k=1` this recovers `4/3`; for `k=2`, the genuinely mixed three-item local bin gives only `6/5`; increasing packet cardinality drives the ceiling toward one. The same conclusion holds if the two packet factors have different individual weights at a vertex: only each **packet sum** matters in this repair. The proof does not guarantee prescribed edge-type frequencies in a decomposition. Unequal profits, packet factors without a two-way global decomposition, or locally different packet cardinalities remain possible escapes.

The factors need not have the same degree. If `P_0,P_1` have constant degrees `k_0,k_1`, the random candidate has `(2+k_0+k_1)n/4` edges and the same repair retains at least `(1+k_0+k_1)n/4`. There are `(2+k_0+k_1)nN/2` edges in total, giving equal-profit ratio at most `(2+k_0+k_1)/(1+k_0+k_1)`. Thus a one-medium versus three-medium split also has ceiling `6/5`. The assumption of globally consistent packet factors still matters.

There is also a conservation check against the simplest bipartite anti-phase realization. If the support is bipartite with shores `L,R`, and `s_i(v)` is the sum of the weights of packet-factor `P_i` at `v`, then `sum_{v in L}s_i(v)=sum_{v in R}s_i(v)` for each `i`, because every physical edge contributes once on each shore. Hence `sum_L(s_0-s_1)=sum_R(s_0-s_1)`. A design that requires `P_0` to have strictly larger packet weight at *every* left vertex and strictly smaller packet weight at *every* right vertex is impossible. This does not exclude alternating signs within each shore or varied heavy thresholds.
