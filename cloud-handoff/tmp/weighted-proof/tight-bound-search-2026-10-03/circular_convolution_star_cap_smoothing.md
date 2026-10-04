# Circular-convolution cap smoothing for a star

Research scratch, 2026-10-03. This proves a limited star statement; it is not a general physical transfer theorem.

Let `0<alpha<1`, `delta=1-alpha`, and let a center have tiny incident target masses `y_i>=0` with `sum_i y_i<=1`. Each leaf is free with a prescribed marginal `p_i>=delta+alpha*y_i`; the center is always free. We may choose any joint distribution of the leaf-free indicators. There is a joint law and a nonnegative flow `f_i` in every state such that

* `sum_i f_i<=1` in every state;
* `f_i=0` unless leaf `i` is free;
* `f_i<=alpha*y_i/delta` in every state; and
* `E f_i=alpha*y_i` for every `i`.

Indeed, on the unit circle choose pairwise disjoint intervals `I_i` of length `alpha*y_i`. Their total length is at most `alpha`, leaving at least `delta` idle length. Let `T` be uniform on the circle and let `W_T` be the positively oriented circular interval of length `delta` starting at `T`. Put

`f_i(T)=|I_i intersect W_T|/delta`.

The intervals are disjoint, so `sum_i f_i(T)<=|W_T|/delta=1`. Also `f_i(T)<=|I_i|/delta=alpha*y_i/delta`. Fubini gives `E|I_i intersect W_T|=delta*|I_i|`, hence `E f_i=alpha*y_i`. The set of shifts `T` for which `f_i(T)>0` has measure at most `|I_i|+delta=alpha*y_i+delta`, even if the interval wraps around zero. Enlarge that active set measurably to measure exactly `p_i`; the added free times carry zero flow. For `alpha=4/5`, the pointwise cap is `4*y_i`.

The law is independent of profit weights and therefore satisfies all coordinate targets simultaneously. This is a constructive explanation of why a common-prefix coupling is suboptimal on a many-leaf star: it staggers the leaves' mandatory free times while preserving their required one-dimensional marginals.

## Extension obstacle

For a bipartite graph, decompose a fractional tiny matching into a unit-matching schedule `M(t)` and convolve its edge-indicator functions by the same circular window. Flow caps and vertex capacities still hold: `f_e(T)<=alpha*y_e/delta`, and `sum_{e incident v} f_e(T)<=1`. The problem is activity support at a vertex. If its base matching activity is split into many separated intervals, the set of shifts with any positive convolved flow may be much larger than `delta+alpha*D_v`, the available free marginal when a heavy object occupies the complementary stock. A schedule in which each vertex's activity lies in one interval would suffice, but existence of such an interval edge schedule on arbitrary bipartite support is an additional nontrivial requirement. Heavy edges also need to be selected integrally in the same states without conflicting with smoothed tiny flow. Thus the star proof does not establish the arbitrary-support smoothing lemma.

Related numerical probe: `unit_heavy_cap4_lp_search.py` enumerates all heavy matchings and solves the capped recourse LP. In 500 random 3x3 and 1200 random 4x4 instances it found no `alpha=4/5` failure; the minimum common factors were about `0.80652` and `0.80125`, respectively. These are numerical tests only.

## Exact extension: unit-heavy pairs with forest interaction support

Suppose each supervertex `i` is a matched pair of ports `(L_i,R_i)` with one unit-weight heavy edge of target occurrence `x_i`. External tiny bundles join any chosen port of one pair to any chosen port of another, and their pair-contracted (undirected) bundle multigraph is a forest, with no parallel two-cycles. No global bipartition is needed. Each pair may also have one internal tiny bundle joining its own ports. For each tiny bundle `e`, let its target mass be `y_e`; assume the standard two port constraints

`sum_{e incident L_i} y_e <= 1-x_i`,  `sum_{e incident R_i} y_e <= 1-x_i`.

Then for every `0<alpha<1` there is a joint law of heavy selected/not-selected states and tiny feasible flows with heavy selection mean `alpha*x_i`, tiny means `alpha*y_e`, and statewise cap

`f_e <= (alpha/(1-alpha))*y_e`.

Construction of a circular interval schedule: root each component of the external pair forest. At a root pair set the common start to zero; if an internal bundle is present, place its interval first on **both** ports, then list the external bundles consecutively on each port. When visiting a child pair, its parent external bundle already has interval `I_p` beginning at `s_p`. If an internal bundle of length `a_i=alpha*y_i^{internal}` is present, place it in `[s_p-a_i,s_p]` on the circle and set the child's common start to `s_p-a_i`; otherwise set the common start to `s_p`. On the contact port list internal (if present), parent, then remaining external bundles consecutively. On the other port list internal (if present), then all external bundles consecutively. Continue recursively. The forest property makes every bundle interval assignment consistent. At each port its incident intervals are disjoint, and both ports' busy sets lie in the common circular arc from `s_i` of length at most

`alpha*d_i`,  `d_i=max(sum_{e incident L_i}y_e,sum_{e incident R_i}y_e)<=1-x_i`.

Apply the window flow `f_e(T)=|I_e intersect W_T|/(1-alpha)` to a uniform circular shift `T`. Each port's flow is at most one, each edge has the stated cap and mean, and the set of shifts for which either port at pair `i` carries positive flow has measure at most

`(1-alpha)+alpha*d_i <= 1-alpha*x_i`.

Enlarge this set to exactly `1-alpha*x_i`, call the enlarged set pair-free, and select the unit heavy edge otherwise. Every tiny flow edge has both endpoint pairs free. Thus heavy and tiny obey capacity one in every state. The construction is independent of profit weights and provides all tiny coordinate means simultaneously. Several parallel *unit-weight* heavy categories on a pair can be selected conditionally on the pair being occupied with relative probabilities `x_{it}/sum_t x_{it}`.

The proof does **not** automatically cover non-unit heavy categories. Their selected states leave positive residual capacity, while the free-set marginal is governed by occurrence stock `sum_t x_{it}`, which can be smaller than the fluid port stock `1-sum_t w_{it}x_{it}`. Nor does it cover cycles or dense external pair-contracted tiny support: a circle interval schedule with one contiguous busy arc at every pair is not established there.

## Uniform finite-palette consequence in the same restricted forest class

This paragraph uses actual physical edges. Let `N` be a positive weighted-degree lower bound. Pair `i` has `k_i` parallel unit-weight heavy physical edges, and every other physical edge `e` has weight `w_e<=tau`. Aggregate tiny physical edges with identical ordered endpoint ports into a bundle `b` of total weight `W_b`; assume the pair-contracted **external bundle multigraph** is a forest. One internal bundle per pair is allowed. The port constraints are

`k_i + sum_{e incident L_i} w_e <= N`,  `k_i + sum_{e incident R_i} w_e <= N`.

Set `x_i=k_i/N` and `y_b=W_b/N`. In the circle construction choose the pair-free set as a **single circular arc** of measure `1-alpha*x_i` containing its convolved-flow-active arc; this is possible because the latter has measure at most `delta+alpha*d_i<=1-alpha*x_i`. Its complement `B_i`, the pair-heavy set, is a single circular arc of measure `alpha*k_i/N`. Choose `M` equally spaced shifts `T_c=(c+theta)/M`, with any fixed phase `theta`. Every circular arc of length `l` contains either `floor(M*l)` or `ceil(M*l)` such shifts (boundary choices can be settled consistently). Hence if `M*alpha/N>=1`, then `B_i` contains at least `k_i` sampled shifts. Select exactly `k_i` of those colors and assign the parallel unit-heavy physical edges bijectively to them; surplus sampled heavy states become empty at pair `i`. This only creates unused capacity and leaves all planned tiny flow feasible.

For each tiny bundle `b`, its assigned base interval `I_b` has length `a_b=alpha*W_b/N`. Split the bundle flow proportionally among constituent physical edges: `f_e(T)=(w_e/W_b)*f_b(T)`. The grid quadrature error is edge-relative and independent of the graph size:

`|sum_{c=1}^M f_e(T_c) - M*alpha*w_e/N| <= (alpha/delta)*w_e/N`.

To see this, write `f_b(T)=delta^{-1} integral_{s in I_b} 1_{s in W_T} ds`. At any fixed `s`, the number of grid shifts whose delta-window contains `s` differs from `M*delta` by at most one; integrate this discrepancy over `I_b`, then multiply by `w_e/W_b`. Thus total planned physical-edge coverage is at least `w_e*alpha*(M-1/delta)/N`.

Fix `0<tau<1/3`, set `s=1-3*tau`, and choose any `0<delta<1`, `alpha=1-delta`, and integer `M` satisfying

`M >= N/(alpha*s) + 1/delta`.

Scale every planned tiny flow by `s`. Its total on each physical edge is now at least `w_e`, while every port/color tiny load is at most `s`. For each tiny physical edge `e`, normalize its positive-flow values over the colors to a probability distribution, for example `p_{e,c}=s*f_e(T_c)/(sum_d s*f_e(T_d))`; the expected physical load in a port/color row is at most the scaled planned flow there because `sum_d s*f_e(T_d)>=w_e`. Each option consumes `w_e<=tau` in exactly its two endpoint/color rows. The manuscript's two-row option lemma (`lem:two`) therefore selects one color for every tiny edge while raising each row by at most `2*tau`. Final tiny load is at most `s+2*tau=1-tau`, and a heavy-occupied port/color row has no positive tiny options at all. Every physical heavy and tiny edge receives exactly one color, with no graph-order or minimum-weight dependence in the palette count.

Optimizing `delta` gives `delta=1/(1+sqrt(N/s))` and

`M = ceil((sqrt(N/s)+1)^2) = N/s + O(sqrt(N))`.

The fixed choice `alpha=4/5`, `delta=1/5` gives the simpler `M=ceil(5*N/(4*s)+5)`. This is a **restricted** physical result for unit-heavy matching pairs whose contracted external tiny bundle multigraph is a forest. For fixed `tau`, the optimized ratio tends to `1/(1-3*tau)` as `N` grows; it approaches one only when `tau` also tends to zero. It is not an unrestricted weighted edge-coloring result. In particular, external cycles (including opposite-orientation two-cycles) remain outside this argument. Non-unit heavy weights require the weaker variant below.

## Non-unit heavy categories: discard residual capacity

The same *physical* construction extends to heavy weights in `(1/2,1]` with a weaker factor. Let pair `i` have `k_i` heavy physical edges of weights `h_{ij}` and total weight `H_i=sum_j h_{ij}`. Assume `N>=k_i` as well as both weighted-degree constraints `H_i+tiny_port_load<=N`. Define

`R=max_i (k_i-H_i)/N`.

Then `0<=R<1/2` (or `<=1/2` if endpoint weight `1/2` is allowed). For the same interval schedule, `d_i<=1-H_i/N`. To place a single pair-heavy arc `B_i` of measure `alpha*k_i/N` outside the convolved tiny-flow-active arc, it suffices that

`delta+alpha*d_i <= 1-alpha*k_i/N`.

This follows simultaneously for every pair whenever `delta<=1-alpha*(1+R)`. Any heavy color selected from `B_i` has zero planned tiny flow at both ports, so its actual residual `1-h_{ij}` can simply remain unused. Choose `alpha=(1-delta)/(1+R)`, `0<delta<1`. The tiny edge flow mean is `alpha*w_e/N`, and all bundle/physical cap and quadrature arguments above still hold. The heavy interval length is `alpha*k_i/N`; an equispaced grid has at least `k_i` shifts in it whenever `M*alpha/N>=1`, and surplus shifts can be cleared before physical assignment.

With `s=1-3*tau`, it suffices to take

`M>=N/(alpha*s)+1/delta = (1+R)*N/(s*(1-delta))+1/delta`.

Optimizing gives `delta=1/(1+sqrt((1+R)*N/s))` and the explicit integer palette size

`M=ceil((sqrt((1+R)*N/s)+1)^2)`.

Thus this restricted forest class admits `M<=((1+R)/(1-3*tau))*N+O(sqrt N)`, at most `(3/2+O(tau))*N+O(sqrt N)` when all heavy weights exceed `1/2`. The result remains independent of graph order and the smallest tiny weight. This does **not** establish the desired bound for arbitrary external support; the forest interval schedule is essential.

## Common-arc scheduling criterion and equal heavy occurrence stock

The quadrature step actually needs no edge-specific interval. Suppose a tiny-flow graph has a measurable base schedule `g_e(t)>=0` on the unit circle with `integral g_e=alpha*y_e` and `sum_{e incident v}g_e(t)<=1` at every port and time. Assume that, for every heavy pair `i`, all base tiny activity at either port lies in **one common circular arc** `J_i` satisfying

`|J_i|+delta <= 1-alpha*x_i`,

where `x_i` is its desired heavy *occurrence* stock. Convolve by the delta-window:

`f_e(T)=delta^{-1} integral_{t in W_T}g_e(t)dt`.

Then each port flow is at most one, `E f_e=alpha*y_e`, and `f_e(T)<=alpha*y_e/delta`. Both ports of pair `i` carry positive flow only when the window meets `J_i`, a shift arc of measure at most `|J_i|+delta`. Enlarge to one free arc of length `1-alpha*x_i` and put heavy outcomes on its complement. For `M` equally spaced shifts, edge-relative quadrature remains

`|sum_c f_e(T_c)-M*alpha*y_e| <= alpha*y_e/delta`.

Indeed, exchange sum and integral: the count of grid windows containing any fixed base time differs from `M*delta` by at most one, and integration against `g_e` costs its total mass `alpha*y_e`. Fragmenting an edge's base support does not worsen the error. If the base schedule and free arcs exist, all the exact-stock and physical two-row rounding steps above apply unchanged.

One dense-support application is **uniform heavy occurrence count**. Suppose every pair has the same number `k` of physical heavy edges, their weights may vary in `(1/2,1]`, and `N>=k` and all port weighted degrees. Let `H_i` be its total heavy weight, `D=max_v(tiny port load_v/N)`, and `R=max_i(k-H_i)/N`. Then

`D <= 1-min_i H_i/N <= 1-k/N+R`.

The tiny target `y_e=w_e/N` has maximum port degree at most `D`. Schedule **all** its edge mass inside the same global circular arc `J` of length `alpha*D` by putting the constant fractional flow `g_e(t)=y_e/D` on `J` and zero elsewhere (if `D=0`, there are no tiny edges). At every port this flow sums to at most one, and every pair's activity lies in `J`. Choose `alpha=(1-delta)/(1+R)`; then `alpha*D+delta<=1-alpha*k/N`, so the criterion holds with one common pair-free arc. The physical palette bound from circle quadrature is

`M=ceil((sqrt((1+R)*N/(1-3*tau))+1)^2)`.

This dense equal-stock class can contain arbitrary fluid cycles and parallel bundles; the forest assumption is unnecessary here. But this common-global-arc construction is essentially the simpler separate-palette baseline below: it reserves a common group of colors for all tiny edges and a disjoint group for heavies. The forest construction genuinely staggers pair activity and uses colors more efficiently when heavy stocks vary.

## A weaker arbitrary-support physical bound from one global arc

There is still a useful baseline when heavy occurrence stocks vary. Let the graph have matching heavy simple support (parallel heavy physical edges on each pair are permitted) and all remaining physical edge weights at most `tau`. Add dummy pairs of heavy count zero for unpaired vertices. Let `N` dominate every weighted port degree and every heavy pair count. Write

`K=max_i k_i/N`,  `D=max_v tiny_port_load_v/N`,  `beta=max(1,K+D)`.

Thus `K,D<=1` and `beta<=2`. Put the constant fractional flow `g_e(t)=y_e/D` on one global arc `J` of length `alpha*D`; no assumption on the tiny support graph is needed. Put

`alpha=(1-delta)/beta`,  `0<delta<1`.

Since `beta>=K+D`,

`delta+alpha*D <= delta+alpha*(beta-K)=1-alpha*K <=1-alpha*k_i/N`

for every pair. Hence every pair-free arc can contain the expanded common activity arc, with a one-arc heavy-occupied complement. The exact-heavy-stock, edge-relative grid quadrature, and physical two-row rounding arguments above apply verbatim. With `s=1-3*tau`, the palette size

`M=ceil((sqrt(beta*N/s)+1)^2)`

suffices. Its leading factor is `beta/s<=2/(1-3*tau)`, independent of graph order and the minimum tiny weight. This is only a baseline: the common arc separates heavy from tiny colors. For unit-heavy pairs, `D<=1-min_i(k_i/N)`, giving `beta<=1+(max_i k_i-min_i k_i)/N`; the uniform-count case has `beta=1`. For non-unit heavy pairs, `D<=1-min_i(H_i/N)` and `beta<=1+K-min_i(H_i/N)`.

A shorter argument gives a sharper count and does not need a circle or bipartiteness. Let `k_max=max_i k_i` and `T_max=max_v tiny_port_load_v=D*N`. Color all heavy edges in `k_max` heavy-only colors, using distinct colors within each matched pair; disjoint pairs do not interfere. Set `Q=ceil(T_max/s)` and give every tiny edge the uniform fractional distribution over `Q` fresh tiny-only colors. Every port/color expected tiny load is at most `T_max/Q<=s`. The two-row option lemma chooses one color per tiny edge and raises each row by at most `2*tau`, so actual tiny load is at most `s+2*tau=1-tau`. Hence

`M_separate=k_max+ceil(T_max/(1-3*tau))`

colors suffice on arbitrary tiny support. This supersedes the preceding `beta` count numerically and is not a tight transfer result.

## Why the exact one-arc condition cannot hold on every support

The common-arc condition is a sufficient scheduling device, not a general theorem. It has a structural obstruction from cyclic interval edge coloring. Let `H` be a connected bipartite graph of maximum degree `Delta` that admits no cyclic interval edge coloring; such examples are given by Asratian, Casselgren, and Petrosyan in [arXiv:1606.09389, Proposition 5.1](https://arxiv.org/abs/1606.09389). Set `a=alpha/Delta`. Replace each edge `uv` of `H` by a pair gadget `P_{uv}` with one tiny spoke to the pair representing `u` and one to the pair representing `v`, each target mass `1/Delta`; orient ports using the bipartition of `H`. At each original-vertex pair all incident spokes use the same chosen port, and at each edge gadget its two spokes use opposite ports. The target tiny port degree is `d_H(v)/Delta` at an original vertex and `1/Delta` at an edge gadget.

Suppose a base schedule for these targets had, at every pair, a **single activity arc of the minimal length** `alpha` times that pair's maximum tiny port degree. At an edge gadget both spokes have integral mass `a` and share an activity arc of length `a`. Port rate is at most one, so both must run at rate one almost everywhere on that same arc. Regard it as one length-`a` interval assigned to the original edge `uv`. At an original vertex, its `d_H(v)` incident intervals are disjoint and exactly fill an arc of length `d_H(v)*a`. Thus they form a continuous circular interval edge schedule of `H` with equal edge lengths.

Choose a maximum-degree vertex to fix one interval start `s_0`. Connectedness and contiguity propagate every edge start as `s_0+k*a (mod 1)` for an integer `k`. If `a=p/q` in lowest terms, label each edge by `k mod q`; incident labels are distinct and consecutive cyclically because adjacent scheduled intervals advance by exactly `a`. Remove any globally unused labels if the definition requires every color used. This is a cyclic interval edge coloring of `H`. If `a` is irrational, `k` is unique and the labels give an ordinary interval edge coloring, hence also a cyclic interval one on a sufficiently large finite palette. Both contradict the choice of `H`. Therefore no such exact one-arc minimal-busy schedule exists for this support, for any `0<alpha<1`.

This obstruction holds for every `0<alpha<1` and concerns the circle-window *method* at zero local arc slack. It does not disprove capped recourse, multi-arc schedules, or a physical weighted edge-coloring bound.
