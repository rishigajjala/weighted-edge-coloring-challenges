# Arbitrary paired residual laws on any fluid star forest: a vertexwise half deficit

**Status: proved.** This extends the prior single-star half-deficit theorem
to arbitrarily many vertex-disjoint fluid stars, even when discrete pairs
link the stars in cycles. Arbitrary marginal laws, arbitrary nonnegative
fluid densities, and arbitrary numbers of discrete pairs are allowed.
It is a theorem for divisible fluid and integer discrete packets; no
uniform asymptotic integer-colouring conclusion for arbitrary original
edge weights is asserted.
Fluid edges have no separate supply bound beyond the capacities at their
two endpoints. This assumption also applies to the correction flows below.

## 1. Independent-base/private-sum lemma

**Lemma.** Let `U` be a sum of mutually independent random variables in
`[0,1]`. Let `Y_1,...,Y_k` have arbitrary prescribed marginal laws in
`[0,2]`. If

`E U + sum_i E Y_i <= 1`,                              (1)

then these variables admit a coupling that preserves the entire
original joint law of the independent summands of `U`, preserves each
`Y_i` marginal, and satisfies

`E(U+sum_i Y_i-1)_+ <= 1/2`.                          (2)

No independence between the `Y_i` or between them and `U` is required
in the resulting coupling.

**Proof, part A: an elementary overflow bound.** For numbers
`z_1,...,z_n in [0,1]`,

`(sum_i z_i-1)_+ <= sum_{i<j} z_i z_j`.                  (3)

This follows by induction. It is clear for one variable. On adding
`z`, write `s` for the old sum. If `s>=1`, the new pair products add
`zs>=z`, enough to pay the overflow increase `z`. If `s<1` and
`s+z>1`, they add `zs>=s+z-1`, because `(1-s)(1-z)>=0`.
The remaining case has no new overflow. For independent bounded
summands with mean sum `m<=1`, taking expectations gives

`E(sum_i Z_i-1)_+ <= sum_{i<j} E Z_i E Z_j <= m^2/2`. (4)

**Part B: one private variable.** Suppose first `Y in [0,2]` is one
variable with a prescribed law and `E U+E Y<=1`. We claim it can be
coupled with the independent summands of `U` so that

`E(U+Y-1)_+<=1/2`.                                (5)

At a fixed mean of `Y`, define `V(law(Y))` as the *minimum* left side
of (5) over couplings with the fixed law of `U`. Mixing two optimal
couplings shows that `V` is convex in the law of `Y`. Every extreme
probability law on `[0,2]` with a fixed mean has support on at most
two points. For finite support this is immediate by perturbing masses
at three support points while preserving normalization and mean.
General laws follow by mean-preserving finite-grid approximation and
continuity: the hinge cost is one-Lipschitz in `Y`, so `V` is
one-Lipschitz in the 1-Wasserstein distance. It therefore suffices to
prove (5) for a two-point law `Y=a+dB`, where `B` is Bernoulli with
probability `p`, `0<=d<=2`, and `a+d p=E Y<=1`. A constant law is
included by taking `d=0`.

Put `U'=U+a` and `m=E U'`. Since `a<=E Y<=1`, the constant `a` is one
more independent `[0,1]` summand; also `m+d p<=1`.

If `d<=1`, choose `B` independent of all summands of `U'`. Then
`U'+dB` is itself a sum of independent `[0,1]` variables with mean at
most one, and (4) proves (5).

If `1<d<=2`, couple `B=1` to the **lowest** probability `p` of `U'`
(using randomization at an atom if needed). The conditional mean in
this lower tail is at most the unconditional mean `m`. For every
`u>=0`,

`(u+d-1)_+-(u-1)_+ <= d-1+min(u,1) <= d-1+u`.

By (4) for `U'`, the expected overflow is at most

`m^2/2+p(d-1+m)`
`<=m^2/2+(1-m)(d-1+m)/d`
`=1/2+(1-m)^2(1/2-1/d) <=1/2`,                    (6)

where the last inequality uses `d<=2`. This proves the one-variable
claim for arbitrary prescribed `Y` laws, while preserving the joint
law of the independent summands of `U`: after choosing a coupling of
`U,Y`, sample the summand vector from its original conditional law
given `U`.

**Part C: many private variables.** Counterquantile-couple the
`Y_i` sequentially. If a running sum has essential support width at
most two, coupling it oppositely by quantiles with the next
`Y_i`, whose width is at most two, makes the new sum's width at most
two. This follows because between two ordered quantiles, the
increase of one summand and the decrease of the other have opposite
signs and magnitude at most two. Lift each step through the
conditional law of preceding variables given their sum. Thus the
aggregate `T=sum_i Y_i` has essential support in `[a,a+2]` for some
`a=ess inf T>=0`. Since `a<=E T<=1`, add deterministic `a` to the
independent base `U`, and apply part B to `T-a in [0,2]`.
Finally sample the `Y_i` vector from its constructed conditional law
given `T`. This preserves every prescribed private marginal, the
entire independent-base law, and the desired overflow bound. `□`

## 2. Vertexwise star-forest rounding

Let the fluid graph be a star forest. Each discrete pair `i` gives
both its endpoints the same random residual capacity `R_i in [0,1]`
with an arbitrary prescribed law; other vertices have fixed
capacity one. Fix any nonnegative mean-feasible fluid flow `y`, so
`sum_{e incident v} y_e <= E R_v` at each paired vertex and at most
one at each fixed vertex.

There is a coupling of **all** pair residuals and state-feasible fluid
flows `Y` such that `0<=E Y_e<=y_e` for every edge and

`sum_{e incident v}(y_e-E Y_e)<=1/2` for every vertex. (7)

Here is the construction. Sample independently every discrete pair
whose endpoints do **not** both lie in one fluid-star component.
Such a pair contributes at most one vertex to each star. Pairs with
both endpoints in one star are private to that star and will be
sampled conditionally below. A pair whose other endpoint lies in no
fluid component may also be sampled in the initial independent stage.

Fix one star with hub residual `X` (`X=1` if fixed). At a leaf `v`
with residual mean `r_v>0`, put the preliminary edge flow
`Z_(ov)=(y_(ov)/r_v)R_v`; if `r_v=0`, mean feasibility forces that
edge's preliminary flow to zero. At a fixed leaf put
`Z_(ov)=y_(ov)`. Every preliminary flow has mean `y_e` and respects
its leaf's state capacity.

If the hub's own discrete partner is a leaf of this star, its
preliminary flow is `cX` for some `0<=c<=1`. Otherwise put `c=0`.
Every other private pair with two leaves contributes a group load
`Y_i=(c_{i,1}+c_{i,2})R_i in [0,2]`. Let `S` be the sum of all
remaining **singleton** preliminary leaf flows, including fixed
ones. Their source pairs are distinct and were sampled independently
in the initial stage. The hub's `X` is independent of all of them:
if its pair is shared, its partner is outside this star; if its pair
is private, draw `X` independently before conditioning the other
private pairs. Thus

`U=1-(1-c)X+S`

is a sum of mutually independent variables in `[0,1]`: the first
summand is in `[c,1]`, and each singleton preliminary flow lies in
`[0,1]`. Mean feasibility at the hub is exactly

`E U+sum_i E Y_i <=1`.                            (8)

Apply the lemma to couple this base with all private leaf-pair loads.
It gives expected overload

`E(sum_{e at hub} Z_e-X)_+`
`=E(U+sum_i Y_i-1)_+ <=1/2`.                       (9)

The coupling in the lemma preserves the complete joint law of the
independently sampled singleton sources and `X`. Hence, conditional
on the globally sampled shared-pair residuals, each star can draw its
own private-pair residuals by the constructed conditional kernel.
Private pairs of different stars are disjoint; these choices can be
made independently across stars conditional on all shared sources.
This creates one globally consistent residual law, even if the
graph of stars linked by discrete pairs contains cycles.

In each realized star, multiply every preliminary flow by the common
factor `min(1,X/sum Z_e)`, taking the factor as one if `sum Z_e=0`.
The resulting flow is hub-feasible and remains leaf-feasible. Its
total lost flow at the hub equals the overload in (9). Any leaf has
only one fluid edge, so its lost flow is at most that overload.
Thus (7) follows, component by component. `□`

## 3. Profit half-gap and mixed configuration theorem

Let `F_q(R)` be maximum feasible fluid profit for nonnegative edge
densities `q`; let `A=F_q(1)` be the all-capacity-one optimum. Apply
the vertexwise theorem to a fluid flow `y` optimal at the mean
capacities, and put `t=E Y`. The nonnegative deficit `y-t` has
incident total at most `1/2` at every vertex by (7). Therefore
`2(y-t)` is feasible at all-one capacities, and

`q·(y-t)<=A/2`.

Because `E F_q(R)>=q·t`, this proves

`E F_q(R)>=F_q(E R)-A/2`.                         (10)

The vertexwise theorem gives a stronger **coordinatewise** statement.
Take any point `(x,y)` of the full local configuration hull of
integer discrete pair packets plus divisible fluid edges on this
star forest. Choose one feasible packet law per discrete pair
realizing the point's expected type counts `x`; its expected pair
load is fixed by those counts. Hence the point's fluid vector `y`
is feasible at the resulting mean residual capacities. Apply the
vertexwise rounding construction to this actual `y`, obtaining a
state-feasible random fluid flow with mean `t<=y` and incident
deficit at most `1/2` at every vertex.

In a **normal** regime of probability `2/3`, sample the discrete
packets and their coupled fluid flow. In the remaining **empty**
regime of probability `1/3`, leave every discrete packet empty and
route the deterministic correction flow `2(y-t)`. This flow is
nonnegative and feasible at all-one capacities by (7). The resulting
distribution is globally feasible and has exact coordinate means

`discrete: (2/3)x`,
`fluid: (2/3)t+(1/3)2(y-t)=(2/3)y`.                 (11)

Thus the global mixed-pattern hull contains two-thirds of the full
local configuration hull **coordinatewise**. Its gap is at most
`3/2` on this fluid-star-forest class, for every nonnegative profit
vector simultaneously. The same pattern distribution works for all
objectives once the input local point is fixed.

This completes the star-forest case even when multiple nontrivial
stars are linked by pair variables around cycles. The proof uses the
star structure to trim at one hub per component, and divisible
fluid to make the preliminary proportional flows and the all-one
completion possible. It does not cover a longer fluid path/tree
component or replace fluid by arbitrary indivisible edge types.

## 4. A stronger bipartite case and sharpness of the general factor

If the **combined** discrete-plus-fluid support is bipartite, the
two endpoints of one discrete pair cannot both be leaves of the same
fluid star: the pair edge and their two spokes would make a triangle.
The only possible pair internal to a star joins the hub to its own
partner leaf. Thus the private double-leaf groups in Section 2 are
absent. Sample *all* pair residuals independently across pairs.
At one star reserve its possible own-partner preliminary edge as
`cX`. Write `H=(1-c)X` for the hub capacity remaining after that
reservation and `S` for the sum of all other preliminary leaf flows.
The summands of `S` belong to distinct pairs, each lies in `[0,1]`,
and they are independent of one another and of `H`. Let
`mu=E S` and `r=E H`; mean feasibility says `mu<=r<=1`.

By the independent-capacity estimate (4)--(5) in
`upper_independent_star_forest.md`,

`E(S-H)_+ = mu-E min(S,H)`
`<= mu-r+r exp(-mu)`
`<= mu exp(-mu) <=1/e`.                           (12)

The same proportional trimming as Section 2 therefore gives
expected incident flow deficit at most `1/e` at **every** vertex,
simultaneously for all stars. Consequently the support-function
fluid gap is at most `A/e`. For a local point `(x,y)`, the normal
regime has probability `alpha=e/(e+1)` and expected fluid flow `t`.
The empty-discrete regime has probability `1/(e+1)` and routes the
deterministic correction flow `e(y-t)`, feasible because each
vertex's deficit is at most `1/e`. Its exact expected coordinates are
`alpha x` and `alpha y`. Therefore

`(e/(e+1)) P subset Q`                              (13)

for the whole bipartite mixed class, without a restriction on how
discrete pairs link fluid-star components. The associated gap is
at most `1+1/e`. The pair residuals remain globally independent,
so cycles among star components cause no gluing issue.

The general `3/2` factor in Section 3 is sharp for this mixed model.
Take a triangle with one unit discrete pair edge `uv` and two unit
profit-density fluid spokes `zu,zv`. The local point putting mean
`1/2` on the discrete edge and fluid amount `1/2` on each spoke has
profit `3/2`. Every global pattern has profit at most one: using the
discrete edge blocks both spokes, while without it the hub capacity
limits total fluid to one. This is a support-function gap of `3/2`.

It also has finite indivisible approximations. For even `B` and
integer `1/epsilon`, take `B/2` unit-weight copies of `uv` and
`B/(2 epsilon)` copies of weight `epsilon` on each spoke. Each local
star packs into exactly `B` bins. All `B/2` unit discrete copies need
colors unavailable to either spoke, while the two spokes need `B`
more colors at their shared hub. Hence
`bp=B` and `chi'_w=3B/2`. This witnesses sharpness of the general
coefficient within the star-forest structure, but it is nonbipartite.
