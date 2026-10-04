# Five-hour exploration: phase-four checkpoint

Written 2026-10-03 around07:43 UTC. New exploration began05:21:17 UTC;
earliest proof-claim time remains10:21:17 UTC and goal counter>=36,069.
At07:42:45 UTC counter26,563, so about2h21m into the requested window.
All new arguments remain **interim candidates**. The unrestricted objective
is not achieved or blocked. No manuscript, Lean, or repository edits were made.
Unrestricted intervals remain bip[4/3,81/50], general[3/2,1999/1000].

This goal turn made substantive progress: a new sharp-looking restricted
mixed-hull route, and elementary partial cases of the capped local policy.

## New matching-heavy/uncapped-fluid candidates

Heavy simple support is a matching, with arbitrary categorical parallel types
on each pair. Fluid has arbitrary support but is divisible and **uncapped**.
Local polytope: categorical sum<=1 per pair, weighted heavy load+fluid load<=1
per vertex. These are not yet physical indivisible-edge coloring theorems.

### Private categorical guards: full-law additive1/4 lemma

Every fluid vertex has at most one guard pair to a private no-fluid leaf.
Allow fixed baseline capacities<=1. At a local-polytope vertex, a positive
fluid component with n vertices,m>=n-1 edges has total effective categorical
freedom<=n-m<=1. Thus at most one guard has a random binary state there.
For q>=0, changing one residual capacity changes recourse at most L times
the change, L=max incident profit<=full-unit recourse on that component.
The two-state Jensen gap is at most p(1-p)|a-b|L<=F_component(1)/4.
Decompose any private local point into vertices, restrict recourse temporarily
to each vertex's positive fluid support, and sum over disjoint components.
This gives a full-marginal guard law with

    E F_q(R)>=q*y-F_q(1)/4.

The guard law can be chosen q-independent; q-specific laws would also suffice.
Fixed guard states stay fixed. Mixing full law4/5 with empty guards1/5 gives
4/5 mean-hull inclusion. Root independently audited this argument.

File: private_single_guard_arbitrary_fluid_five_fourths_candidate.md.

### Bipartite matching-heavy graph: forest gluing

At a GLOBAL local-polytope vertex each heavy pair has at most one effective
categorical degree of freedom: either none/type or two types summing to1.
Its live column is c(e_u+e_v), c!=0. Positive fluid columns are e_u+e_v.
All live columns must be independent. Bipartiteness then makes their combined
support a forest (any even cycle has an alternating kernel vector).

Contract positive-fluid components. Fractional heavy links form a forest and
cannot lie inside a fluid component. Deterministic heavy pairs may be anywhere;
fix them as baseline loads. Apply the private full-law lemma separately to each
fluid component. Shared fractional links have identical categorical marginals,
so glue component laws conditionally along the contracted forest. Deterministic
links stay fixed, avoiding their possible cycles. Finally use ONE GLOBAL
empty/full coin. The empty state cancels the sum of the1/4 losses, giving
candidate4/5 inclusion for all bipartite matching-heavy/uncapped-fluid inputs.

Root and forest agent independently checked fixed baseline capacities,
categorical kernels, forest gluing, and support-function separation. No main
unrestricted claim. The existing four-vertex mixed example tends to factor5/4,
so this candidate would be sharp within its restricted class.

File: bipartite_matching_heavy_arbitrary_fluid_five_fourths_candidate.md.

### General graph: odd pseudoforest and a cycle-coupling switch

Without bipartiteness, independent live incidence columns form an odd
pseudoforest: each component is a tree or a single odd unicycle. After fluid
components are contracted, fractional heavy links form a pseudoforest.

If a cycle contracts to one component, there is one internal random heavy
pair. At a local vertex it changes two capacities. The same Jensen bound
costs at most p(1-p)(L_u+L_v)<=F_component(1)/2. Attached trees glue normally.

For a cycle through k>=2 fluid components, first build private full laws.
Choose the cycle component C with smallest F_C(1). Glue all other cycle
components as a path, inducing a target joint law on C's two cycle-link bits
A,B. Both original and target laws have the same one-bit marginals. Their
2x2 table differs only in theta=P(11), by |delta|<=1/2.

**Transport lemma, including branch guards Z:** To increase theta bydelta,
take delta mass from10 anddelta from01; change10->00 (A becomes lighter,
recourse cannot decrease) and01->11 (A becomes heavier, recourse loss at most
delta F_C(1)). Keep all Z states unchanged samplewise. This preserves the
full joint marginal of Z and the individual A,B marginals. Reverse via
11->01 and00->10. Thus replacing the cycle-pair coupling costs at most
F_C(1)/2, including arbitrary branch-state correlations. Sample C's other
states conditional on the target(A,B), then glue its attached branch trees.

Total loss<=sum F_i(1)/4+min_cycle F_i(1)/2<=sum F_i(1)/2 for k>=2.
Together with k1, one global full/empty mixture2/3,1/3 gives a candidate
2/3 inclusion for matching-heavy+uncapped-fluid in GENERAL graphs. Root
derived the branch-preserving transport lemma; forest agent independently
audited it and is updating the saved proof. Triangle is the tight3/2 example.

File being updated: general_matching_heavy_odd_cycle_reduction_candidate.md.

Scope is crucial: heavy pairs are vertex-disjoint. Turning one cycle bit on
must remain a feasible heavy state; this fails for arbitrary heavy support.
Fluid has no per-edge cap, and no physical integer-color transfer is supplied.

### A discrete scoped corollary to check

For bip matching-heavy support with ALL small edges having the SAME weight s,
put k=floor(1/s). A heavy type leaves r_h=floor((1-w_h)/s) small slots. Replace
its weight in the mixed model by H_h=(k-r_h)/k. Local normalized small counts
then have exactly the mixed capacity inequalities. Conditional residual
capacities timesk are integers, and bip bmatching recourse is integral, so the
mixed5/4 hull candidate should extend to repeatable integer-count patterns in
this uniform-small-weight class. Forest agent was asked to audit this.
The graded-path4/3 lower uses heterogeneous small weights, so no contradiction.
Uniform physical coloring transfer still needs proof separately.

## Capped reciprocal-max policy: new analytic partial cases

The K=4/3 rule remains open for uncapped probes with competitors at BOTH ends.
Agent proved and root independently checked:

1. All one-star probes, including capped ones. For an uncapped probe with
   base b=K a/(p_u p_v), the competing endpoint load T has mean<=16/9 and
   mean-b<=4/3. Lower convex envelope of f(t)=1/max(1,t) on[b,infinity) has
   tangent point t0=1+sqrt(1-b). Split b at32/81. If b>=32/81, envelope at
   16/9 equals9/16; below it, mean-b<=4/3 yields37/64>9/16. If b>=1, Jensen.
2. All cap-active two-sided probes. Write U=1+3D_u,V=1+3D_v, UV<16/9,
   b=12a. Tangent f(t)>=1-t/4 and max(Tu,Tv)<=b+Cu+Cv reduce to a mean
   inequality. Set a=min(Du,Dv), WLOGU<=V. The gap times9UV/4 equals
   UV(14-9U)+4U^2-9, increasing inV forU<=4/3; atV=U it is
   9[U^2(2-U)-1]>=0.

File: one_star_reciprocal_policy_lemma.md.

Moment-only relaxation may suffice for the remaining case. For competitor
sum X at endpoint with s=D-a,p=(1+3D)/4:

    EX<=mu=K s/p,
    Var X<=K^2 s h(min(s,1/3))/p^2,
    h(t)=3t(1-t)/(1+3t).

Padding X by mu-EX makes its mean exactlymu without increasing variance,
and only lowers the probe objective. Thus arbitrary independent distributions
with these moments legitimately relax the original competitor sums.
Root alternated grid LPs over121-point distributions,120 endpoint triples,
three starts: no violation of E reciprocal>=9/16. At a0,D_u=D_v1 relaxed
minimum~.571996>9/16. Overall equality is the known a1/3 one-star face.
Agent performed outer DE/random tests, likewise no failure. These are NOT
certificates. Mean-only relaxation fails at b0: X,Y each2 withprob2/3 gives
E reciprocal5/9<9/16. Actual variance bound excludes that distribution.

Files: two_star_moment_relaxation.py/.json (root), plus agent moment scans.
Agent auxiliary conjecture Emax<=16/9 for b>=32/81 also survived tests;
small b does not satisfy that simpler bound. No proof yet.

Agent saved star_forest_physical_transfer_candidate.md: one-star rule may
make the unbounded-star-degree physical bridge unconditional, but bridge
itself still needs a full audit. General arbitrary-support capped policy open.
Uncapped5/4 hull result does NOT imply bounded conditional flow K*y. A capK>=4
is necessary in a tiny-target two-guard example; no sufficient universalK yet.

## Lower-bound and alternative-route diagnostics

- Root audited uniform_rank_triangle_factor_network_three_halves.md: five
  profit-ray proof is sound in its stated two-distinct-blocker/uniform-spoke-
  rank scope. Mixed ranks remain outside it.
- Several shared-blocker multi-port mixed-rank tests did not exceed4/3;
  uniform three-phase(1,2,3) star choices have a simple one-item alternative
  that prevents compounding at uniform blocker profit. Exact small physical
  LP tests around1.055 are diagnostics only.
- A proposed XOR role-twist factor cycle caused an agent correction/retraction
  exchange; do not rely on its verbal parity argument without reading the
  final saved note. Regardless, its balanced random-half calculation gives
  at most4/3, not a stronger lower bound.
- Stronger agent factor-law barrier, independently checked by root: if each
  whole factor already has a feasible joint law of its small-edge choices and
  incident blocker states, and blockers form a matching across factors, write
  S=total local small profit,A=sum q_e p_e,P=sum q_e. Independent factor laws
  plus selecting a blocker only when both endpoints request it gives profit
  >=S+sum q_e p_e^2>=S+A^2/P. All blockers givesP. Hence local/global ratio
  <=(S+A)/max(P,S+A^2/P)<=max_{0<=p<=1}(1+p-p^2)=5/4. The original vertex-
  local LP need NOT have coherent whole-factor laws. Repeated bundle counts,
  rather than single binary spokes, are necessary to exploit this gap.
  Root suggested a focused incoherent hub point: bundle weights(.4,.3,.26),
  max counts(2,3,3), hub counts(1,1,1), blocker means(.5,2/3,2/3), normalized
  spoke profits(.5,1/3,1/3). Hub mixed profit7/6 beats every pure normalized
  bundle profit1, whereas port marginals use full bursts. Lower agent is
  investigating physical shared-blocker networks at such points.
- Root tried a broader upper route: all fixed slot-shape palettes plus harmonic
  remainder, on finite weights i/W. For each mode, nested Hall slot constraints
  are checked against all integer bin partitions. LP costs W12~1.43694,
  W16~1.47503,W20~1.504386. W20 already suggests this fixed-shape route does
  not reach1.5. Numerical LP optima, not exact universal lower certificates.
  Do not expand a huge grid; the route looks weaker than the structural lead.
  Files: slot_shape_cover_lp.py, slot_shape_cover_W12/W16/W20.json.
- Web primary search confirmed Goemans–Pan2609.17932 concerns stronger
  knapsack-intersection LP for general demand matching but provides no new
  closing theorem here. Avoid confusing stock-capped demand matching or
  varying vertex capacities with this repeatable-count/unit-capacity problem.

## Runtime and agents

All root computations closed: sessions89383(moment),42493(W16),55846(W20).
No root subprocess remains live. All three agents remain active:

- extend_paired_fluid_forest: write/audit general odd-cycle transport proof,
  uniform-small discrete consequence, then broader heavy-support boundary.
- five_hour_physical_rounding: remaining reciprocal inequality, then whether
  uncapped5/4 can be made capped uniformly; physical bridge kept separate.
- bipartite_lower_new_mechanism: genuinely mixed-size physical count gadgets.

Continue substantive research. The five-hour minimum is not yet met. Do not
claim the new restricted arguments as settled theorems until further audit
and the time threshold; do not present them as the unrestricted solution.

Late updates: forest agent audited the uniform-small-weight discrete count
corollary and completed the general cycle-transport proof in its saved note.
A k2 contracted-cycle diagnostic is an ordinary5cycle with two disjoint unit
heavy links and three fluid edges, all localmeans1/2. At scaled heavy marginals
alpha/2, optimized total unit-profit fluid recourse is2-alpha independent of
the coupling; target3alpha/2 obstructsalpha>4/5 only. Thus its full-law loss is
F(1)/4, not1/2. The generic cycle repair may be nonsharp for cyclesk>=2; this
does not improve the general class because the k1 triangle is tight3/2.
Physical agent notes independentpair activation cannot realize4/5 uncapped:
singlefluidedge y=D_u=D_v=.3 hasp=.2+.8*.3=.44, overlap.1936<.24 target.
Correlated heavy schedules are essential for the new4/5 route.
