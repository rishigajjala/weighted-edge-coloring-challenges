# A 4/3 count-certificate barrier for branched guarded forests

**Status.** This is a rigorous obstruction to one lower-bound *certificate*, not an upper bound on the weighted chromatic index. It extends the nonuniform graded-path count barrier to arbitrary branching, arbitrary physical multiplicities, and heterogeneous guard weights. The graph may have parallel edges; its core is a rooted forest after parallel bundles are suppressed.

## Model and statement

Orient every core bundle away from the root. Every core edge has weight strictly between `1/3` and `1/2`. At each core vertex `v`, attach any number of private leaf edges of weights strictly greater than `1/2`. We assume every guard at `v` is incompatible with every incoming core edge at `v`, meaning their weights sum to more than one. No compatibility condition is imposed on outgoing core edges and guards.

Write `a_v`, `b_v`, and `g_v` for the numbers of physical incoming core edges, outgoing core edges, and guards at `v`. Let `M=sum_v a_v=sum_v b_v` be the number of core edges, `G=sum_v g_v` the number of guards, `T=M+G`, `n` the number of core vertices, and `B=bp(G)`. Then

    3T + sum_v |b_v-g_v| <= 4Bn.                    (1)

Moreover every feasible color contains at most `n` physical edges. Therefore the standard all-items-equal counting certificate `T/n` cannot exceed `4B/3` in this entire model. A different price certificate or a different coloring obstruction is not ruled out.

## Proof of the local inequality

Fix `v` and an optimal local packing in at most `B` bins. A guard must be alone among the guards and cannot share with an incoming core edge. It can share with at most one outgoing core edge, since a guard weighs more than `1/2` and two core edges each weigh more than `1/3`. Thus the `g_v` guard bins absorb at most `g_v` of the `b_v` outgoing core edges. The remaining `a_v+(b_v-g_v)_+` core edges need at least half as many additional bins, because three core edges cannot fit. Consequently

    2B >= 2g_v+a_v+(b_v-g_v)_+.                    (2)

Let `P=sum_v(b_v-g_v)_+` and `Q=sum_v(g_v-b_v)_+`. Summing (2) and using `sum a_v=sum b_v=M` gives

    2Bn >= 2G+M+P.

Since `M-G=P-Q`, twice this inequality becomes

    4Bn >= 4G+2M+2P
         = 3(M+G)+(P+Q)
         = 3T+sum_v|b_v-g_v|,

as claimed.

## Proof of the per-color assignment

Fix a feasible color. Each core bundle contributes at most two edges, since its weight exceeds `1/3`. If it contributes one, assign that edge to the child endpoint. If it contributes two, assign one edge to the parent and one to the child. Assign each guard edge to its core endpoint.

The assignments are injective. A vertex receives at most one assignment from its unique incoming bundle. It receives an assignment from an outgoing bundle only when that bundle contributes two edges. This consumes more than `2/3` load at the vertex, so no other core edge or guard can occur there in this color. If the vertex receives an assignment from an incoming core edge, it cannot also have a guard edge by the incompatibility assumption. At most one guard can occur at a vertex, since guards weigh more than `1/2`. Thus each core vertex receives at most one assignment. Every edge of the color is assigned, proving the `n` bound.

For a singleton root (or a forest with isolated core vertices), the same argument applies. Parallel core edges are counted as physical copies of their parent-child bundle, so the proof allows arbitrary multiplicity.

## Meaning and limits

The original path-plus-leaves family is a special case. Branching and nonuniform demands cannot make its equal-per-edge count certificate cross `4/3`; equation (1) also identifies a penalty for mismatch between outgoing core multiplicity and guard multiplicity. The proof does **not** show `chi'_w(G)<=4B/3`, because some colorings might require more colors than the all-items-equal certificate detects. It also does not cover a core vertex with two incoming bundles, a non-tree core, core weights outside `(1/3,1/2)`, or guards that can share incoming edges.

## Finite diagnostics

The accompanying scripts enumerate all repeatable feasible integer count patterns for small instances and optimize a dual price against local bin hulls. `bipartite_mixed_path_search.py` sampled 600 mixed-weight caterpillars; `bipartite_cycles_branch_search.py` sampled 2,500 even-cycle or binary-tree cores. Weight numerators came from `{4,5,6,7,8,9,12}` over capacity 12. Neither run found a ratio above `4/3`. `bipartite_two_size_search.py` sampled 3,000 instances with complementary weights `5/12` and `7/12` and found no gap above one, consistent with the already proved exact two-range lemma. These searches are diagnostics only; local numerical LPs and random sampling do not certify a universal statement.
