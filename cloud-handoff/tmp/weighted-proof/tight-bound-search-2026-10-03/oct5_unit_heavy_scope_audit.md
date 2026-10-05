# Scope audit: unit-heavy/tiny physical coloring is already covered

5 October 2026. This corrects the research priorities; it is not a new unrestricted bound.

The current manuscript already proves the bipartite harmonic-charge bound
chi'_w(G) <= A(G)+o(n), where a(w)=1/floor(1/w), A=max_v sum a(w_e), and n=bp(G).
Its general-charge-finish lemma, together with the same parallel grouping and Shannon's ordinary multigraph coloring, also implies the coarser general bound
chi'_w(G) <= (3/2)A(G)+o(n).
Indeed the full groups form H with d_H(v)+Q_R(v)<=A+O(bn), while the remainder R has bounded multiplicity. A palette K >= (3/2)(A+O(bn))+eta*n both properly colors H by Shannon and leaves K-d_H(v)>=Q_R(v)+eta*n. The finishing lemma colors R with a further o(n) cost. All parameters are chosen in the manuscript's order, uniformly in graph order and minimum weight.

Consequently, when every edge has weight exactly 1 or at most tau,
A(G) <= Delta_w(G)/(1-tau) <= bp(G)/(1-tau),
because a(1)=1 and a(w)<=w/(1-w)<=w/(1-tau) for w<=tau. Thus the existing methods give coefficients 1/(1-tau) in the bipartite case and 3/[2(1-tau)] in the general case, up to o(bp). For every epsilon>0, taking tau sufficiently small already gives 1+epsilon and 3/2+epsilon respectively, with arbitrary heavy topology and arbitrary tiny support. For a fixed positive tau, this statement does not erase the O(tau) term.

The recent capped activation, unit-guard stars, bridge motifs, and adaptive unit-heavy smoothing results are valid abstract tools at their stated scopes, but should not be presented as new physical coloring theorems for this already-covered regime. In particular, further numerical sharpening of bounded-degree unit-heavy smoothing does not address the main gap.

The unresolved physical improvement must use residual capacity of mixed heavy weights below 1, or compatible medium-size edges. If a bin contains a heavy edge of weight just above 1/2 and almost 1/2 tiny load, its harmonic charge is almost 3/2 despite actual bin load 1. A proof that treats every heavy edge as a unit guard discards exactly the capacity needed for the desired stronger bound.

Relevant current manuscript locations: lem:harmonic-load; lem:general-charge-finish; lem:bp-mult-round. No manuscript or Lean source was changed in making this audit.
