# Fixed hybrid capped recourse: global reduction and current obstruction

5 October 2026. Scratch research only. This note does **not** prove the desired
`2/3` fixed-law inequality for arbitrary branching. The global reduction below
is exact; numerical probes are diagnostics only.

## Exact cap-concavity reduction

Fix the allowances `D` and the disjoint guard-pair partition. Consequently
the hybrid activation law is fixed while the target fluid vector varies. Let

`P(D)={z>=0: Σ_{e∋v} z_e <= D_v for every v}`.

For an active set `A`, write `F_q(A,C)` for the maximum nonnegative-profit
fluid value with vertex capacities `1_A` and edge caps `C`. It is jointly
concave and coordinatewise nondecreasing in `C`: a convex combination of
optimal feasible flows for two cap vectors is feasible for the corresponding
convex-combination cap vector. Every `y∈P(D)` is a convex combination
`y=Σ_k λ_k z^k` of extreme points. If `C>=12y`, then, statewise,

`F_q(A,C) >= F_q(A,12y) >= Σ_k λ_k F_q(A,12z^k)`.

Thus proving the desired expectation inequality for **every extreme point**
`z∈P(D)` with caps exactly `12z`, for the same fixed `D` and hybrid law,
proves it for every feasible `y` and `C>=12y`. This does not justify
replacing `y` by a `q`-optimal point subject to the original fixed caps;
the temporary component caps `12z^k` may exceed the original `C`.

In an extreme point, the positive columns of the unsigned vertex-edge
incidence matrix are linearly independent. Therefore every connected
positive-support component is a tree or an odd unicyclic graph. Two parallel
positive edges are impossible. This follows because an even cycle gives an
alternating kernel vector, any component with at least two cycles has more
edges than vertices, and a single odd cycle has nonsingular unsigned
incidence matrix. Conversely the support statement is only necessary:
active degree rows and zero coordinates decide which such supports are
actually extreme. This reduction removes arbitrary multiple-cycle support,
but **does not remove branching**, odd cycles, or same-shore paired guards.

The recourse objective adds over vertex-disjoint fluid components statewise.
Consequently guard pairs linking different fluid components cause no extra
difficulty for a support-function inequality: their shared bit changes the
joint law, but expectation of the sum uses each component's marginal law.
If no guard pair has both endpoints in one fluid component, all activation
bits within each component are independent vertex bits with probabilities
`(1+2D_v)/3 >= 1/4+3D_v/4`. Monotonicity and the audited capped
independent-vertex theorem then give the stronger `3/4` transfer on every
fluid component, including arbitrary branching and nonbipartite support.
For a bipartite fluid component whose internal paired endpoints lie on
opposite shores, the existing capped opposite-shore exchange gives the same
`3/4` transfer. The unresolved structure is internal same-shore guard
pairs, together with odd unicyclic fluid components.

## Why modewise or simple local surplus cannot close the gap

Independent pair activation by itself fails `2/3` even on a two-leaf star:
center allowance `3/4`, the two leaves one guard pair with allowance `3/8`,
and target `3/8` on each spoke. With unit-profit and caps at least one,
independent-mode recourse is `(5/6)(7/12)=35/72 < (2/3)(3/4)=1/2`.
The comonotone mode alone can also fail: an always-free center with three
spokes of target `1/3`, each leaf in a distinct guard pair of allowance
`1/3`, and caps at least one, has comonotone recourse `5/9<2/3`.
The mixture balances opposite kinds of loss. Neither mode can be bounded
at the target factor separately.

The exact comonotone identity may be useful for a quantitative invariant.
For any nonnegative recourse objective, with `A_s={v:D_{pair(v)}>=s}`,

`E_comono F_q(A,C) = (1/3) F_q(V,C) + (2/3)∫_0^1 F_q(A_s,C) ds`.

Hence the hybrid expectation is `3/4` times independent-pair expectation
plus `(1/12)F_q(V,C)+(1/6)∫_0^1F_q(A_s,C)ds`. The all-free term is a real
global reserve, but alone supplies only `q·y/12`; it cannot pay an
arbitrary high-profit core target without a statewise allocation argument.
The existing uncapped private-spoke surplus `(1−s)/3` is unavailable for
small capped spoke mass: one spoke of mass `s<1/12` has cap `12s`, so even
its all-free recourse is `12s`, which vanishes with `s`.

## Numerical diagnostic

`oct4_hybrid_branch_probe.py` sampled 2,500 pair-partitioned graphs with
2–4 guard pairs, random feasible targets and profits; its least observed
hybrid ratio was about `0.77476`. `oct4_hybrid_extreme_probe.py` sampled
5,000 random graphs, optimized a linear profit over `P(D)` to obtain an
extreme target, and used exact `C=12y`; its least observed ratio was about
`0.77227`. Both minima came from two-spoke motifs, not branching examples.
These finite random samples neither prove the global lemma nor establish
the sharp constant. The scripts enumerate every guard state and solve the
conditional flow LP with SciPy HiGHS.

## Separate boundary for adaptive heavy laws on nonmatching support

If one broadens from disjoint guard pairs to an arbitrary unit-heavy
triangle, a fixed finite cap multiplier cannot achieve the **exact**
`2/3` scale. Put heavy target `(1−s)/2` on each triangle edge and one
fluid target `y=s` on a fluid edge between vertices 1 and 2, with cap
`C=Ks<1`. At scale `alpha`, every integral heavy matching has at most one
edge and its prescribed heavy marginals force

`Pr(empty)=1−(3alpha/2)(1−s)`.

Every nonempty triangle edge blocks one of the fluid endpoints. Therefore
`E fluid <= Ks[1−(3alpha/2)(1−s)]`; achieving `alpha s` requires

`K >= alpha/[1−(3alpha/2)(1−s)]`.

At `alpha=2/3`, this diverges as `s→0`; at `alpha=2/3−epsilon`, it yields
the necessary `K >= alpha/(1−3alpha/2)`, asymptotically `4/(9epsilon)`.
This does **not** obstruct the disjoint-pair theorem, and it does not
obstruct an asymptotic `2/3−epsilon` theorem with `K(epsilon)` large.
It shows why an uncapped fractional-matching inclusion cannot be smoothly
converted to a fixed cap-12 policy for arbitrary heavy topology by a
black-box truncation.

## Sharp capped smoothing with arbitrary heavy topology and matching fluid support

There is a positive result at exactly the triangle's scale when the
**simple positive fluid support is a matching**. This is a separate,
`q`-independent joint-law theorem, not a proof for fluid branching. Heavy
unit edges may have arbitrary graph topology and parallel identities.
Parallel fluid identities between one matched pair may be grouped into one
bundle, as explained below.

Fix `K>=1` and put `alpha=1/(3/2+1/K)`. Let `x_h>=0` be heavy targets,
`y_e>=0` fluid targets, and assume

`Σ_{h∋v}x_h + Σ_{e∋v}y_e <=1`

at every vertex, with `C_e>=K y_e`. For each fluid matching edge (or
parallel bundle) define `c_e=min(1,K y_e)` and a **dummy matching-edge**
coordinate

`r_e=alpha y_e/c_e=alpha max(y_e,1/K)`.

For heavy edges use coordinates `z_h=alpha x_h`. The vector `(z,r)` is in
the ordinary matching polytope of the multigraph consisting of heavy edges
and fluid dummy edges.

To verify vertex constraints, at a vertex of one fluid edge `e`, heavy
target load is at most `1−y_e`. If `K y_e>=1`, its augmented load is at
most `alpha(1−y_e)+alpha y_e=alpha`. If `K y_e<1`, it is at most
`alpha(1−y_e+1/K)<=alpha(1+1/K)<=1`. A vertex with no fluid edge has
augmented load at most `alpha`.

For an odd vertex set `S` of size `2m+1>=3`, heavy target mass on its
internal edges is at most

`|S|/2−(1/2)Σ_{v∈S}fluid_target_load(v)`.

Each internal strong fluid dummy edge (`Ky_e>=1`) adds `alpha y_e`,
which cancels the heavy upper bound's subtraction for that edge. Each
internal weak dummy edge adds at most an **extra** `alpha/K` over its
target `alpha y_e`. Because the fluid support is a matching, there are
at most `m` internal weak dummy edges. Boundary fluid target only
strengthens the bound. Thus the augmented internal mass is at most

`alpha(2m+1)/2 + m alpha/K <= m`,

where the gap on the right is exactly `alpha(m−1)/2>=0`. These are all
Edmonds matching-polytope inequalities, so `(z,r)` is a convex
combination of integral matchings.

In each matching state, take its heavy identities; for each selected
fluid dummy edge carry `c_e` fluid. The matching makes the vertex
capacity constraints automatic, and `c_e<=C_e`. Heavy expectations are
`alpha x_h`; fluid expectations are `r_e c_e=alpha y_e` exactly. For a
parallel fluid bundle with total target `Y`, use one dummy edge with
`c=min(1,KY)` and, when selected, split its flow in proportions `y_e/Y`.
Each identity then carries at most `K y_e<=C_e` and has the right mean.

The coefficient is sharp for this method and for a universal theorem
with these assumptions: the heavy triangle and a tiny fluid edge from
the preceding section force `alpha<=1/(3/2+1/K)` as `s→0`. The same
dummy-edge proof cannot handle a branching fluid support: weak dummy
edges each require incidence `alpha/K`, regardless of how tiny their
target is, so arbitrarily many weak edges at one vertex violate the
matching-polytope degree inequality. This pinpoints a concrete place
where a continuous flow policy must replace one-dummy-edge selection.

### Bounded simple fluid degree

The same construction does give a graph-order-uniform result for any
fixed maximum **simple fluid-support degree** `Delta>=1`, allowing
branching. Group parallel fluid identities by endpoint pair, with bundle
target `Y_e` and total cap at least `K Y_e`; use one dummy edge per bundle
and distribute selected flow proportionally to the original targets.
Set

`alpha_Delta=2/[3(1+Delta/K)]`, `c_e=min(1,KY_e)`, and
`r_e=alpha_Delta max(Y_e,1/K)`.

At every vertex, the augmented heavy-plus-dummy matching degree is at
most

`alpha_Delta[1+Delta/K]=2/3`.

For an odd set `S` of size at least three, each internal strong dummy
edge cancels its subtraction from the heavy internal-mass bound; each
internal weak dummy edge costs less than `alpha_Delta/K` extra. There
are at most `Delta |S|/2` internal dummy edges. Hence total augmented
internal mass is at most

`alpha_Delta |S|(1+Delta/K)/2=|S|/3 <= (|S|−1)/2`.

Edmonds decomposition again yields one law with exact heavy means
`alpha_Delta x` and fluid means `alpha_Delta y`, respecting each cap.
For any fixed `Delta` and `epsilon>0`, taking `K` of order
`Delta/epsilon` gives `alpha_Delta>=2/3−epsilon`. This is weaker than
the sharp matching-support result at `Delta=1`; its loss grows with
simple fluid degree and does not settle unbounded branching. It is an
adaptive joint law, not the originally proposed fixed hybrid law.

A sharper coefficient follows when `Delta>=2` and `K>=5 Delta`:

`alpha=1/(3/2+3/K)`.

The vertex augmented degree is at most
`alpha(1+Delta/K)<= (2/3)(6/5)=4/5`. An odd set of size three has at most
three internal simple fluid bundles, so its augmented internal mass is
at most `alpha(3/2+3/K)=1`. For an odd set of size `s>=5`, the preceding
degree count gives augmented internal mass at most
`alpha s(1+Delta/K)/2 <= (4/5)s/2 <= (s−1)/2`. Thus all matching
inequalities hold. To achieve any coefficient `2/3−epsilon`, it suffices
to choose `K=O(Delta+1/epsilon)` with an absolute implied constant.
This refined proof still fails when `Delta` is unbounded; its dummy-edge
probabilities consume too much matching degree at a high-degree hub.

## Open step

For the fixed hybrid law, prove a quantitative inequality on an extreme
tree or odd unicyclic support with internal same-shore guard pairs, allowing
branching and high-price edges. A leaf deletion needs a surplus term because
the removed leaf's mate changes reduced recourse. A viable invariant must
account for both the exact comonotone threshold integral and the cap-limited
profit obtainable from small spokes. No such invariant is established here.

## Independent audit of the separate two-bin port 8/9 lemma

The local lemma in `oct5_two_bin_port_phase_barrier.md` is correct at its
stated repeatable-bin scope. For a rank-three bin with sorted weights
`1/4<x<=y<=z<1/2`, `x+y+z=1`, the alternative integer bins
`(0,0,2)`, `(1,2,0)`, `(2,0,1)` are feasible. Mixing them with
probabilities `1/3,4/9,2/9` gives each coordinate expectation `8/9`.
For the claimed sharp example `(x,y,z)=(.30,.34,.36)` with unnormalized
profits `(2,3,4)`, any feasible bin contains at most three items. Direct
enumeration by item count gives maximum profit eight among all bins other
than `(1,1,1)`, attained by the three alternatives; the original has
profit nine. Thus `8/9` is sharp for this universal **local** replacement.

It does not supply a global edge-consistent law. In the displayed
replacement mixture, the count of the smallest type has tails
`Pr(X>=1)=2/3`, `Pr(X>=2)=2/9`; the middle type has tails `4/9,4/9`.
If one physical edge is assigned the smallest role at one endpoint and
the middle role at the other, any coupling of these two specified local
count distributions satisfies

`E min(X,Y) <= min(2/3,4/9)+min(2/9,4/9)=2/3`.

The `8/9` local coordinatewise expectation therefore cannot be glued
naively across differently typed ports. Another local law or a global
coupling argument could do better; the calculation only audits this
particular replacement mixture.

## Mixed-weight guard pivot: quantile-order obstruction

The degree-two mixed-weight theorem
`oct4_mixed_heavy_comonotone_degree2_transfer.txt` uses real residual
capacities and a pure common occupancy threshold. Its simple moment
policy overflows at high-allowance branching vertices. A tempting
extension would compare its real residual law with binary comonotone
activation at the same mean residuals, then reuse the unit-guard star
argument. This comparison is false even on a guarded two-spoke star.

Let the center's guard pair have one weight-`1/2` type with target `x=1`.
Its mean residual allowance is `D_c=1/2`; under common occupancy at
scale `2/3`, its actual residual is `1/2` for `U<=2/3` and `1`
otherwise. Let each of two leaves belong to a distinct unit-guard pair
with target `x=3/10`, so each leaf has `D_l=7/10` and residual `0`
for `U<=1/5`, `1` otherwise. Give each spoke target `1/4`, cap at least
one, and unit profit. The real common-occupancy recourse is

`(2/3−1/5)(1/2)+(1/3)(1)=17/30`.

Binary comonotone capacities with the same means have center-free
probability `2/3` and leaf-free probability `4/5`, so their recourse is
`2/3`. Thus real comonotone recourse is strictly **lower**. The
residual distributions cross: although the leaves have higher means,
their low quantile is zero while the center's is one half. No coupling
can order these residuals pointwise by their means. This refutes only
the binary-comonotone domination shortcut, not the desired hybrid or
mixed-weight transfer theorem. A 400,000-sample numerical scan of the
two-leaf one-pair star under the 3/4 independent plus 1/4 common
occupancy law found minimum ratio about `0.6797`, with guard weights
near one; this is a nonexhaustive diagnostic.
