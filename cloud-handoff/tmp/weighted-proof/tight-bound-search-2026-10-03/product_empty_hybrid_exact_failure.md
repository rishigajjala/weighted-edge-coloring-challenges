# A fixed product/empty hybrid fails for paired unit-heavy fluid recourse

This tests only the stated heavy-state law, not the `2/3` mixed convex-hull
inclusion. Let `1/2 < epsilon < 1`. Use unit heavy edges `uv` and `cc'`
with local presences `x_uv=1-epsilon/2` and `x_cc'=1-epsilon`.
The only fluid edges are `cu,cv`, each with unit profit and target
`y=epsilon/2`. The local target is feasible: every leaf has load one,
and the center has load `1-epsilon+epsilon=1`.

Set `alpha=2/3`. In mode I (probability `3/4`), independently sample
the two heavy-pair states with marginal `alpha x`. Thus the leaf pair is
free with probability `p_L=(1+epsilon)/3`, the center with probability
`p_C=(1+2epsilon)/3`, and unit-profit fluid recourse has expectation
`p_L p_C`.

In mode II (probability `1/4`), with probability `2/3` sample the two
full-marginal heavy states independently, and with probability `1/3`
leave all heavy edges absent. This mode also has heavy marginals
`alpha x`. Its fluid recourse expectation is
`(2/3)(epsilon/2)epsilon+1/3=(1+epsilon^2)/3`.
The fluid edges may be taken uncapped, or assigned caps at least one;
whenever the center and the leaf pair are free, one unit can be routed
over one spoke.

The hybrid's expected optimal fluid profit is therefore

`(3/4) p_L p_C + (1/4)(1+epsilon^2)/3
  = (2+3epsilon+3epsilon^2)/12`.

The required scaled target profit is `alpha(y_cu+y_cv)=2epsilon/3`.
Their difference is

`(2+3epsilon+3epsilon^2)/12 - 2epsilon/3
  = (1-epsilon)(2-3epsilon)/12 < 0`

for `2/3 < epsilon < 1`. At `epsilon=3/4`, the law gives exactly
`95/192 < 1/2`. Since even optimal fluid recourse under this fixed
heavy law misses the support objective, no conditional fluid policy
can repair it. A different correlated heavy law can; the example does
not refute the mixed-hull target.

The failure explains a subtle difference between the full-product/empty
mode and a comonotone *scaled-marginal* mode. The former spends its global
empty probability on cases where a full-marginal product draw could have
already freed both sources. The latter couples the two scaled free events
directly and gives their intersection probability `min(p_L,p_C)=p_L`.
