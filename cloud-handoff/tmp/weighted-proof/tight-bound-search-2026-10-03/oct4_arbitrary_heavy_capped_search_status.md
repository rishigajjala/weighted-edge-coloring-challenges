# Arbitrary heterogeneous heavy support: 4 October search status

This note records a substantive but inconclusive one-color search. It does not claim an arbitrary-heavy capped `3/4` transfer or a physical coloring bound.

## Exact finite mixed-hull feasibility LP

Fix a finite bipartite heavy multigraph with edge types `h`, weights `w_h`, a bipartite tiny support with targets `y_e`, and caps `C_e=12y_e`. Let `M` range over all heavy matchings, and let `R_v(M)=1−sum_{h in M,h at v}w_h`. The target `alpha(x,y)` belongs to the capped one-color mixed hull exactly when there are nonnegative matching-state masses `p_M` and tiny state flows `f_{M,e}` satisfying

`sum_M p_M=1`, `sum_{M:h in M}p_M=alpha x_h`, `sum_M f_{M,e}=alpha y_e`,

`f_{M,e}<=C_e p_M`, and `sum_{e at v}f_{M,e}<=R_v(M)p_M`.

This LP tests **simultaneous** tiny-coordinate means, not a single profit vector. The equivalent support-function target is, for all heavy prices `c_h in R` and tiny profits `q_e>=0`,

`max_M [sum_{h in M}c_h + F_q(R(M),C)] >= alpha[sum_h c_h x_h + sum_e q_e y_e]`.

`heterogeneous_capped_full_hull_search.py` generated feasible local `x,y` on random small bipartite instances and solved this LP. In 2,000 sampled instances at `alpha=3/4`, none was infeasible; another 2,000 at `alpha=.85` also gave none. At `alpha=.9`, an infeasible instance occurred by trial 96. These are floating-point, nonexhaustive experiments and give no proof of the `3/4` statement.

The `.9` failure has a simpler exact one-edge explanation. Take two disjoint heavy edges incident to opposite endpoints of a tiny edge: the first has weight `1/2` and full marginal one, the second has weight one and full marginal `1/2`. The tiny target is `y=1/2`, feasible at both endpoints. At scale `alpha`, the free events have probabilities `1−alpha` and `1−alpha/2`; maximal expected tiny recourse is obtained by nesting these events and equals `1−3alpha/4`. The target is `alpha/2`, so `alpha<=4/5` is necessary. The cap `12y=6` is inactive. Taking the first heavy weight slightly above `1/2` gives thresholds approaching `4/5`. This calibrates the LP; it is **not** a `3/4` obstruction.

## Stronger universal-heavy-law probe

For a fixed heavy fractional vector `z=alpha x`, put `p_v=1−sum_{h at v}w_hz_h`, and let `Phi_q(p)` be capped recourse under independent Bernoulli active vertices. A potential stronger structural theorem would produce one heavy matching law with marginals `z` and `E F_q(R(M),C)>=Phi_q(p)` for every `q>=0`. The path diagnostic in `heterogeneous_pipage_chord_exact_obstruction.md` shows that an arbitrary alternating-path rounding **fails**, while a correlated completion repairs that specific instance.

`heterogeneous_universal_law_probe.py` tested one matching law against 12–20 sampled tiny-profit directions simultaneously (including coordinate directions). In 100 random small heterogeneous bipartite instances at `alpha=3/4`, the finite LP found no incompatible set of directions. Earlier fixed-profit searches likewise found no violation. These tests are weak evidence only: the full set of profit directions is infinite, and a negative result would refute the stronger domination route, not necessarily the mixed-hull inclusion.

## Structural bottleneck

Common conditional **mean** weight in each connected heavy component gives a proof by aggregate matching pipage and opposite-shore covariance; see `common_mean_capped_heavy_transfer_audit.md`. With arbitrary bundle means, an alternating path can change weighted residuals at many internal vertices. The exact path example proves that independent completion can lose capped recourse, yet shows the loss can be repaired by long-range correlation between heavy edges that become disconnected after the first pipage step. Current experiments found no exact `3/4` infeasibility. A proof would need a correlated matching law or a direct mixed-hull integrality-gap argument beyond ordinary local pipage; a counterexample would need to violate the full simultaneous LP above.
