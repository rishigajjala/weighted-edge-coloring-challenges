# Demand matching and exact local knapsack hulls: primary-source audit (4 Oct 2026)

## Model and what would transfer

For one color, a physical edge \(e=uv\) of weight \(d_e\) is selected once and consumes the **same** \(d_e\) at **both** endpoints. Each vertex has capacity 1. Write

\[
K_v=\operatorname{conv}\{\mathbf 1_S:S\subseteq\delta(v),\ \sum_{e\in S}d_e\le 1\},\qquad
P=\bigcap_v K_v,\qquad
I=\operatorname{conv}\{\mathbf 1_M:M\text{ is globally feasible}\}.
\]

This is the uniform-capacity, physical-edge version of **Knapsack-LP** in Goemans–Pan [GP26]. It is stronger than the natural load LP \(\sum_{e\ni v}d_ex_e\le1\): it includes *every* valid local knapsack inequality. A normalized coloring with \(N\) colors gives a point \(x_e=1/N\) in \(P\), because the \(N\) local color bins at each vertex form a convex decomposition.

The one-color integrality gap \(\beta=\sup_{q\ge0}h_P(q)/h_I(q)\) has a direct geometric meaning: by separation and downward closure, \(\beta\le c\) implies \(c^{-1}P\subseteq I\). Thus a sharp gap at most \(4/3\) on bipartite graphs, or \(3/2\) in general, would imply the respective *fractional one-color* transfer. It would **not alone** produce exact physical stock across finitely many colors; the palette rounding/quantifier bridge remains separate. Conversely, a valid lower witness must provide \(x\in P\), not merely the load inequalities.

## Directly applicable paper

[Michel X. Goemans and Yuchong Pan, “A Better-Than-3 Approximation Algorithm for Demand Matching via Knapsack Intersection LP and Contention Resolution,” arXiv:2609.17932 (15 Sep 2026)](https://arxiv.org/pdf/2609.17932), especially §§1.1, 4, 5 and Appendix A.

* Their demand matching uses one edge demand \(d(e)\) at both endpoints, exactly our two-incidence coefficient rule, but permits arbitrary vertex capacities \(b(v)\) and a profit objective. Their Knapsack-LP is \(\bigcap_vK_v\) (p. 3, lines 100–124 in the PDF). Their exact simple-graph upper gaps are **2 for bipartite** and **\(3/2+\sqrt2\approx2.914\) for general graphs** (pp. 4–5). These are genuine exact-local-hull results, but weaker than \(4/3\) and \(3/2\).
* The paper explicitly lists determination of the exact Knapsack-LP gaps as open (p. 19, concluding remarks). It does not supply a lower witness beyond the desired thresholds for this hull.
* Its table of 3 general, 2.5 bipartite multigraph, and about 2.699 bipartite simple lower gaps is expressly for **Natural-LP** (p. 2), so none can be imported as a Knapsack-LP lower bound without checking the local integer hull.
* The proof samples an exact feasible local configuration independently at each **source-side** vertex. On a simple bipartite graph, proposals arriving at each sink are independent; a sharp \((q,1/(1+q))\)-balanced contention-resolution scheme for the *integral knapsack polytope* then gives 1/2 survival at \(q=1\) (pp. 3–4). Appendix A makes this scheme tight via one capacity-filling item competing with many unit items. This is only an obstruction to that **independent-proposal scheme**; a different globally correlated matching law could exceed 1/2, so it is not a gap witness for \(P\).
* In multigraphs, parallel proposals at a sink are correlated. Their repair bundles feasible subsets of parallel edges into auxiliary multiple-choice items and rounds an **MC-Knapsack-LP** (pp. 15–19), obtaining \(2+\varepsilon\) bipartite and \(3/2+\sqrt2+\varepsilon\) general approximation ratios. The authors explicitly ask whether these bounds can be obtained by rounding the original physical-edge Knapsack-LP directly (p. 19). Hence the simple-graph gap proof should not be quoted as an established exact gap bound for the original multigraph \(P\).

## Nearby results that do not give the sought witness

* [Adam Jozefiak, F. Bruce Shepherd, and Noah Weninger, “A Knapsack Intersection Hierarchy Applied to All-or-Nothing Flow in Trees,” arXiv:2201.02914](https://arxiv.org/pdf/2201.02914) defines the \(t\)-row hull hierarchy, with \(t=1\) equal to our local-knapsack strengthening. Its \(\Omega(n/t)\) lower examples concern all-or-nothing **path-flow requests on a tree**. A request can occupy many tree-edge rows, unlike a demand-matching item occupying exactly its two endpoint rows. These examples establish no two-column local-hull gap.
* [Nikhil Bansal, Nitish Korula, Viswanath Nagarajan, and Aravind Srinivasan, “On \(k\)-Column Sparse Packing Programs,” arXiv:0908.2256](https://arxiv.org/pdf/0908.2256) studies arbitrary nonnegative entries in each column and obtains a \(2k-1\) lower gap for **its own strengthened LP**. The paper distinguishes graph demand matching by the additional equal-nonzero-entry restriction (pp. 1–2). More decisively, its construction has a size-1 item and size-\(\varepsilon\) items sharing a unit-capacity row (p. 9). The claimed fractional point assigns almost 1 to *every* item, but the exact local knapsack hull imposes \(x_{\mathrm{big}}+x_{\mathrm{small}}\le1\), which it violates. Thus this lower example fails the local-hull test even before the equal-endpoint-demand test. The two-column-sparse label alone is insufficient.
* [Shavit, “A minimum witness for the \(3/2\) configuration-linear-program gap in two-weight graph balancing,” arXiv:2608.13318](https://arxiv.org/pdf/2608.13318) gives a six-job \(K_4\) witness (four size-1 cycle jobs and two size-2 diagonal jobs), with integral makespan 3 versus configuration-LP value 2 (pp. 2–3). Every job has the same size at either possible machine, but a schedule **orients it to one endpoint**. Demand matching selects an edge and charges **both endpoints**. Thus this visually suggestive configuration gap is not a lower bound for weighted edge coloring or demand matching.

## Scope checks and useful direction

The Goemans–Pan upper bounds allow arbitrary \(b(v)\), so they apply to our uniform \(b(v)=1\) subcase (after rational scaling). A **lower** example with unequal \(b(v)\), however, would not automatically specialize to uniform capacity. A binary-item lower example also need not survive an asymptotic blowup: copies of one type may coexist in a color, changing both local configurations and global feasible sets. Any proposed coloring lower bound must be checked afresh after replication, including its \(bp\) denominator.

The most promising reusable idea here is the exact-local-configurations-at-one-shore interface, not the 1/2 numerical bound. To reach \(3/4\) bipartite retention, one would need a **coupled** source configuration law or a two-sided recourse argument that exploits compatibility of local decompositions; the sharp independent-sampling CR theorem shows that merely improving the sink repair step cannot suffice in general. For multigraphs, the paper's multiple-choice bundling is an explicit warning that physical parallel categories cannot be treated as independent proposals. No source examined here establishes or refutes the desired \(4/3\) bipartite or \(3/2\) general exact-local-hull gaps.
