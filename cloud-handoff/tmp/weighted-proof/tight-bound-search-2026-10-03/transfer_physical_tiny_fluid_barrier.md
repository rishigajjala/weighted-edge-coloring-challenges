# Transferring the star-forest fluid theorem to physical tiny edges

**Status.** Two exact findings: the preliminary star flow from an
`N`-bin physical input obeys each bundle's *total* physical stock
cap, but naive tiny-edge fluidization can inflate both the local and
global one-pattern optima by `3/2` even as tiny weights tend to zero.
The latter is a barrier to that transfer step, not a lower bound above
`3/2` for weighted edge colouring. It explains why the unbounded-count
tiny-fluid reduction cannot be imported into the finite-stock model.

## 1. A positive total-stock cap for the mixed construction

Suppose actual physical edges are locally packed into `N` bins at every
vertex. Choose one endpoint's induced `N`-bin histogram for each
discrete pair packet; let its residual capacity have law `R` and mean
`r`. In a fluid bundle `e` incident with a leaf of a star, let `T_e`
be the **total physical weight** of all tiny edges in that bundle.
The mean fluid demand obtained by replacing those edges by their
aggregate load is `y_e=T_e/N`.

The preliminary flow used by
`upper_arbitrary_paired_star_forest_half_deficit.md` is

`Z_e=(y_e/r)R` if `r>0`, and zero if `r=0`.

Because the law of `R` is uniform over an actual list of `N` bins,
every residual value in its support satisfies `R<=N r`: the sum of
the `N` listed residual values is `N r` and all are nonnegative.
Consequently

`Z_e <= (T_e/Nr)(Nr)=T_e`.                        (1)

The same calculation applies when the leaf is the hub's own discrete
partner; a fixed leaf has `Z_e=T_e/N<=T_e`. Proportional hub trimming
only lowers the flow. In the empty-discrete correction branch, its
flow is `2(y_e-t_e)<=2T_e/N<=T_e` when `N>=2`; in the sharper
bipartite branch it is `e(y_e-t_e)<=eT_e/N<=T_e` when `N>=e`.

Thus every fluid colour from this construction respects each
bundle's **aggregate** physical tiny-edge stock weight. If `T_e>0`,
one may define a common tentative inclusion fraction
`x_{f,c}=f_{e,c}/T_e` for every physical tiny edge `f` in bundle `e`.
It lies in `[0,1]`, agrees at both endpoints, and its weighted sum on
the bundle equals `f_{e,c}`. Across the complete fractional palette,
these fractions cover each physical tiny edge exactly once, because
the construction realizes the aggregate demand `T_e` exactly.

This does **not** make the tentative fractions locally packable in
each colour. A positive fluid amount can occupy less capacity than
the weight of any single physical tiny edge. The bounded-multiplicity
rounding lemma in the manuscript requires its per-colour edge vector
to lie in the actual local knapsack hull; the aggregate stock cap
does not supply that hypothesis. It also requires individually small
per-colour inclusion fractions and bounded physical multiplicity.

## 2. A uniform finite-stock fluidization barrier

For integer `k>=2`, take a star centered at `z` with `2k` leaves
`u_1,...,u_(2k)`. Give each spoke `zu_i` **one physical edge** of
weight `1/k` and profit `1/k`. Attach a private vertex `v_i` to each
`u_i` by **one physical discrete edge** of weight
`1-1/(2k)` and profit `1/k`. The discrete support is a matching,
the tiny support is one fluid star, and the combined physical support
is a tree.

At `u_i`, its two physical edges cannot share one pattern:

`(1-1/(2k))+1/k =1+1/(2k)>1`.

They have equal profit `1/k`. Therefore every original global
pattern has profit at most `2k*(1/k)=2`; selecting all discrete
edges attains two. The same per-leaf local inequality gives local
configuration optimum at most two, also attained by the all-discrete
point. Hence

`L_original=C_original=2`.                        (2)

Now replace each single spoke edge by divisible fluid of density one,
with no physical stock restriction on its continuous amount. Choose
all `2k` discrete edges. Every `u_i` has residual capacity `1/(2k)`;
send precisely that amount of fluid on every spoke. The hub receives
total fluid load one. The discrete profit is two and fluid profit is
one, so this one globally feasible **fluidized** pattern has profit
three. No fluidized pattern can exceed three, since total discrete
profit is at most two and the hub's fluid profit is at most one.
Thus

`L_fluid=C_fluid=3`.                              (3)

The inflation ratio is exactly `3/2` for every `k`, while the tiny
edge weight `1/k` tends to zero. Each fluidized spoke carries only
half of one physical tiny edge's weight in the maximizing pattern;
that edge cannot fit at its leaf alongside the discrete edge.

This example specifically uses finite stock. If the tiny spoke type
were repeatable without its physical one-copy cap, omitting one
discrete edge would permit `k` copies on that spoke and recover nearly
the same profit in the original count model. That is why the
unbounded-count tiny-fluid reduction in
`../tiny-fluid-and-large-profit-bucket-reduction.md` does not
contradict (2)--(3).

The physical graph itself has `bp=chi'_w=2`: put all discrete edges
in one colour; partition the `2k` tiny spokes into two groups of `k`
and assign each discrete edge to the opposite one of those two
colours from its spoke. The barrier concerns the fluidization
comparison and the direct per-colour conversion, not the desired
original colouring coefficient.

## 3. What a valid transfer still needs

Equation (1) removes one possible concern: the mixed construction
does not overuse a bundle's *total weight* when started from actual
`N`-bin histograms. The missing operation is to redistribute tiny
edge fractions among colours so that every positive use of a
physical edge fits at **both** endpoints in that colour. It must
preserve enough per-edge coverage and control the lost weighted
degree uniformly in the number of leaves/bundles. The example in
Section 2 shows that simply replacing each tiny edge by divisible
load before the local-to-global comparison can lose a constant
factor, even on a tree and even when the tiny threshold tends to
zero. Any use of the manuscript's bounded-multiplicity physical
rounding lemma must first supply its actual local-hull and
small-per-colour-fraction hypotheses; the mixed theorem alone does
not do so.

There is an exact local slack criterion that isolates the remaining
problem. Let physical tiny items have weights at most `delta`, let
`0<=x_f<=1`, and suppose their expected load in one colour is at
most `C-delta`, where `C` is the residual capacity after its discrete
packet. Then `x` belongs to the true one-colour knapsack hull of
subsets with load at most `C`. To see this, repeatedly choose two
fractional coordinates and vary them in opposite weighted directions
so their total weighted load stays fixed. Randomly take one of the
two boundary points with probabilities preserving both coordinate
expectations. Each step makes at least one coordinate integral.
When at most one fractional coordinate remains, round it randomly;
the realized load rises by at most its weight, hence at most
`delta`. Every resulting subset is `C`-feasible and has the desired
inclusion marginals.

Obtaining this absolute slack by deleting all flows at leaves whose
residual capacity is below `delta` is **not** a uniform repair. In
the maximizing fluidized pattern of Section 2, every leaf residual
is `delta/2`, so that deletion removes the entire unit fluid load
at the star hub despite `delta=1/k` tending to zero. A successful
transfer must first move much of that load to different colours or
change the discrete packet-state coupling; simple per-colour
threshold deletion cannot pay for it.
