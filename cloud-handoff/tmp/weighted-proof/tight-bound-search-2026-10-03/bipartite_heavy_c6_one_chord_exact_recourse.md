# Exact one-chord recourse on a heterogeneous heavy six-cycle

**Status, 2026-10-03:** a proved sparse diagnostic for the q-specific recourse program, not a counterexample to the target `alpha=3/4` transfer. The heavy simple support is a bipartite six-cycle, so it is outside the forest restriction. All fluid is divisible.

Label the heavy cycle edges cyclically `e_1,...,e_6`. Give `e_1,e_4` weight `h in (1/2,1]` and give the other four edges weight `1`. Put local heavy marginals `x_e=1/2` for all six edges. Add one fluid chord joining the opposite-shore vertices incident to `(e_1,e_6)` and `(e_3,e_4)`. Its local capacity is `y=(1-h)/2`, and setting it to `y` meets both endpoint capacity constraints exactly. This is a valid categorical-heavy-plus-fluid local point.

At scale `alpha`, prescribe one-color heavy marginals `a_e=alpha/2`. For a heavy matching `M`, write

`R_1(M)=1-h 1_{e_1 in M}-1_{e_6 in M}` and

`R_4(M)=1-1_{e_3 in M}-h 1_{e_4 in M}`.

The chord's one-color recourse is `F(M)=min(R_1(M),R_4(M))`. For every matching `M` of the cycle,

`F(M) <= (2-h)-1_{e_1 in M}-(1-h)1_{e_2 in M}-(1-h)1_{e_3 in M}-1_{e_6 in M}`.  (1)

To verify (1), if `e_6 in M`, then `F=0` and the right side is nonnegative since at most one of adjacent `e_2,e_3` can be selected. If `e_1 in M`, then `e_2,e_6` are absent and the right side is `(1-h)(1-1_{e_3 in M})`; when `e_3` is present the other chord endpoint has residual zero, and otherwise `F<=1-h`. If neither `e_1` nor `e_6` is present, then `R_1=1`, while at most one of `e_2,e_3` is present, so the right side is at least `1`. This proves (1). Taking expectations with the prescribed marginals gives

`E F(M) <= (2-h)(1-alpha)`.

For `2/3<=alpha<=1`, equality is attained as follows. Choose each of the three opposite-edge pairs `{e_1,e_4}`, `{e_2,e_5}`, `{e_3,e_6}` with probability `1-alpha`; choose each of the two alternating perfect matchings with probability `3alpha/2-1`. The five probabilities are nonnegative and sum to one. Every heavy edge has marginal `(1-alpha)+(3alpha/2-1)=alpha/2`. The first pair gives chord recourse `1-h`, the second gives `1`, and the remaining three states give `0`. Therefore the exact q-specific optimum is

`W(alpha)=(1-alpha)(2-h),  2/3<=alpha<=1`.

The required fluid marginal at scale `alpha` is `alpha(1-h)/2`. At `alpha=3/4`, `W` exceeds the requirement by factor `2(2-h)/[3(1-h)]`, which tends to `2` as `h downarrow1/2` (not a tight obstruction). The inequality fails for this local point if `alpha > 2(2-h)/(5-3h)`; as `h downarrow1/2`, the threshold tends to `6/7`. This gives a ceiling on a much stronger transfer factor for this *mixed fluid model*, but does not affect the target `3/4` statement or the physical weighted-edge-coloring problem directly.
