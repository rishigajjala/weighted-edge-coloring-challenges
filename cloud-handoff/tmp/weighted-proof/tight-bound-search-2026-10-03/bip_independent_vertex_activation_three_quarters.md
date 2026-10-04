# Independent vertex activation: exact bipartite three-quarter theorem

Date: 2026-10-03. Scratch result; no manuscript or repository files changed.

## Theorem

Let \(G=(V,E)\) be a finite bipartite graph, let \(q_e\ge0\), and let
\(D_v\in[0,1]\). Set \(p_v=(1+3D_v)/4\), independently retain each vertex
\(v\) with probability \(p_v\), and write \(G[A]\) for the resulting induced
graph. Then

\[
 \mathbb E\,\nu_q(G[A])\ \ge\ \frac34 F_q(D),\qquad
 F_q(D)=\max\left\{\sum_e q_e y_e:
 y_e\ge0,\ \sum_{e\ni v}y_e\le D_v\ (v\in V)\right\}.
\]

Here \(\nu_q\) is maximum *integral* matching weight. The constant is sharp:
for one unit-profit edge with \(D_u=D_v=1/3\), the left side is \(1/4\),
while \(F_q(D)=1/3\).

## Forest lemma (the induction actually used)

Suppose \(H\) is a forest, \(y\ge0\) is supported on its edges, and
\(\sum_{e\ni v}y_e\le D_v\le1\). With independent vertex activations
\(p_v=1/4+3D_v/4\),
\[
 \mathbb E\,\nu_q(H[A])\ge\frac34\sum_{e\in E(H)}q_e y_e.
\]

Proof by induction on the number of positive-support edges. Isolated
vertices can be ignored. Choose a leaf \(v\), its unique neighbor \(u\),
and put \(e=uv\), \(t=y_e\). Let \(H'=H-v\), retain the other flows, and
replace the capacity of \(u\) by \(D'_u=D_u-t\); all other capacities stay
as before. This leaves the restricted flow feasible, and the new activation
probability of \(u\) is \(p'_u=p_u-(3/4)t\). Both probabilities are valid.

Condition on the activations of all vertices except \(u,v\). In \(H'\),
let \(M_0\) be the maximum matching weight if \(u\) is absent, and let
\(M_1=M_0+B\) be the maximum if \(u\) is present. Since leaving \(u\)
unmatched is possible, \(B\ge0\). In the full graph, when \(u,v\) are
both present, the optimum is
\(\max(M_1,q_e+M_0)=M_0+\max(B,q_e)\): a matching either omits \(uv\),
or takes it and cannot use \(u\) elsewhere. Therefore the conditional
expectation for \(H\), minus that for \(H'\) at the reduced activation
probability \(p'_u\), is exactly
\[
 \frac34tB+p_up_v(q_e-B)_+.
\]
Feasibility gives \(D_u,D_v\ge t\), hence
\[
 p_up_v\ge(\tfrac14+\tfrac34t)^2\ge\tfrac34t,
\qquad
 (\tfrac14+\tfrac34t)^2-\tfrac34t
       =\frac{(1-3t)^2}{16}.
\]
The conditional difference is thus at least
\(\frac34t[B+(q_e-B)_+]\ge\frac34tq_e\).
Average over the conditioning and apply induction to \(H',D',y'\).

## Passage to arbitrary bipartite graphs

Choose an extreme optimal solution \(y\) of the displayed fractional
matching LP. Its positive support is a forest: any cycle in a bipartite
graph is even, and alternating \(+\varepsilon,-\varepsilon\) along it
preserves every vertex degree; for sufficiently small positive
\(\varepsilon\), both perturbations are feasible, contradicting
extremality. Let \(H\) consist of the positive-support edges of \(y\).
The forest lemma gives
\(\mathbb E\nu_q(H[A])\ge(3/4)\sum q_ey_e=(3/4)F_q(D)\).
For every activation outcome, \(H[A]\subseteq G[A]\), so
\(\nu_q(G[A])\ge\nu_q(H[A])\).

The assertion concerns independent *vertex* activation and nonnegative
edge profits; it does not claim an analogous theorem for independent edge
activation or non-bipartite graphs. The induced matching is chosen after
the activation outcome is known.

## Diagnostic

The prior numerical probe bip_vertex_activation_forest_probe.py tested
20,000 weighted trees on 4--8 vertices with capacities from a rational
grid and nonnegative weights. It found no value below \(3/4\); the best
case was an effective single edge at \(D=1/3\). This computation is
ancillary; the proof above is exact.
