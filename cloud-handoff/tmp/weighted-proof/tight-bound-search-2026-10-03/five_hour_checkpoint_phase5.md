# Five-hour search checkpoint, phase 5

Written 2026-10-03 08:44 UTC. This records interim research, not a new
unrestricted proof claim. The fresh five-hour window began 05:21:17 UTC;
no new proof claim before 10:21:17 UTC **and** goal time counter 36,069 s.
Latest counter at 08:43:20 was 30,197 s. The main goal is still open.
The established manuscript intervals remain bipartite [4/3,1.62] and
general [3/2,1.999]. Manuscript, Lean, and private repository unchanged.

## New analytical progress

1. **Common heavy weights, arbitrary bipartite heavy support, uncapped
   divisible fluid:** full candidate in
   `arbitrary_bip_common_heavy_weight_five_fourths_candidate.md`.
   Root and forest agent audited it. Complete every local load row with
   a zero-profit private fluid slack edge. At a heavy-degree-tight
   vertex, equal incident heavy weights allow row splitting into a
   heavy-only row and a fixed-residual fluid row. After scaling heavy
   columns, the active matrix is bipartite incidence; extremality makes
   its positive support a forest. Contract fluid components. Each fluid
   factor admits a private-guard full-marginal law losing at most K_C/4;
   one-hot heavy-only factors glue along the forest. One global empty
   state with probability 1/5 cancels the losses, giving 4/5 inclusion.
   The input-wide condition can be one common weight per heavy connected
   component. A pointwise extreme suffices if positive heavy weights are
   equal at every categorical-tight vertex; slack vertices may have
   heterogeneous categorical guards. Unequal weights meeting at a tight
   vertex are the precise unresolved obstruction. Still no fluid caps
   or physical integer palette in this result.

2. **Two-capacity dual lemmas:** opposite-shore joint increase and
   same-shore equal swap have Jensen loss <=p(1-p)hK. The same-shore
   proof is particularly short: minimal left dual prices give
   -B<=pi_u-pi_v<=A, where A=max_j(q_uj-q_vj)_+ and
   B=max_j(q_vj-q_uj)_+. Opposite signs attain at different neighbors,
   so A+B<=K by a two-edge matching. For opposite shores, a
   coordinatewise minimal cover dual satisfies pi_u+pi_v<=K: either
   uv is tight or tight incident edges at u,v are disjoint. These
   independently verify both parities of the one-fluid-tree common-
   weight alternating-heavy-path reduction. See agent notes including
   `opposite_shore_two_capacity_lipschitz.md`.

3. **Arbitrary heterogeneous heavy support with unheavy fluid-star
   centers:** `bipartite_unheavy_star_forest_five_fourths_candidate.md`.
   Fluid stars are vertex-disjoint and each center has zero heavy
   marginal. Order leaves by profit. A laminar quota flow network
   decomposes x into heavy matchings where top-2 and top-3 covered counts
   are each floor/ceil of their means, simultaneously on both shores.
   At each chosen matching, properly color its links touching top-4
   leaves in four phases (auxiliary bip multigraph max degree 4); all
   other selected heavy links get phase 5. Delete one uniform phase.
   Heavy marginals become 4x/5. Prefix fluid recourse:
   k=1 follows its mean; k>=4 has >=4/5; k=2 and 3 have formulas
   2/5+(3/5)F_full and 3/5+(2/5)F_full. Balanced covered counts and
   weights>=1/2 give Jensen gaps C2<=1/3, C3<=1/2, enough for 4/5.
   Layer-cake integration yields all q. Root independently derived the
   two gap bounds and checked quota/phase structure; full note deserves
   one final read. Does not handle heavy centers, arbitrary fluid trees,
   or capped/physical small edges. This phase method stops at 5 phases
   under those sharp abstract count gaps.

4. **Circle smoothing and a genuine finite-palette interface in a
   restricted physical class:**
   `circular_convolution_star_cap_smoothing.md`.
   Unit-heavy support is a matching. Contract each pair into two ports;
   external tiny bundles must form a multigraph forest (opposite port
   orientations between the same two pairs create a forbidden 2-cycle).
   Same-endpoint parallel physical tiny edges can be aggregated. Root
   the pair forest; assign one interval of length alpha*y_b per tiny
   bundle, so each pair's two port busy sets lie in one shared arc of
   length alpha*max(D_L,D_R). A delta=1-alpha circular window gives
   mean alpha*y and cap alpha*y/delta, while pair active support has
   length <=delta+alpha*D. Heavy times are a complementary interval.
   A grid of M equally spaced shifts has per-physical-edge quadrature
   error <=alpha*w_e/(delta*N), independent of graph order/min weight.
   With s=1-3tau and M>=N/(alpha*s)+1/delta, scale flow by s, retain
   exact heavy identities, and apply the manuscript's two-row option
   lemma to color all tiny physical edges (each <=tau). Optimizing gives
   M=ceil((sqrt(N/s)+1)^2). **Fixed tau tends to 1/(1-3tau), not 1**;
   near-one requires tau->0 or tau chosen for desired epsilon.
   Internal tiny bundles can also be included: place their common
   interval first at both ports, and at a child shift its common start
   backward from the parent interval start by the internal length.
   Agent is updating this extension. No non-unit heavy residuals or
   external pair cycles covered. Root audited arithmetic and interface.

5. **Whole-edge partial-rounding interface:** in
   `forest_optimum_l1_sensitivity_and_palette_gap.md`, given flows
   Z_e(c), set p_e,c=Z_e(c)/max(w_e,sum_c Z_e(c)); remaining mass is an
   uncolored option. Colored choices meet two endpoint/color rows;
   uncolored choices meet two endpoint residual-stock rows. The two-row
   lemma adds at most 2tau to each row. Thus only vertex total deficit
   U_v=sum_e(w_e-sum_c Z_e(c))_+ needs control. The general nonlinear
   simultaneous selection gap is still open. Per-edge empirical control
   is unnecessary, but an expectation/union bound is insufficient.

## Lower-bound exploration / barriers

`unequal_graded_guard_paths_four_thirds_ceiling.md` gives an independently
audited interim forward-coloring argument for arbitrary decreasing core
weights below 1/2, arbitrary unequal bundle demands d_i, and d_i private
complementary outgoing guards (terminal guard count may be arbitrary).
Let k_i=floor(1/w_i), q_i=ceil(d_i/k_i), B=bp. With M=ceil(4B/3),
incoming occupancy <=ceil(4q_prev/3) leaves >=floor(d_i/3) empty colors
after placing guards. Fill up to k_i outgoing copies per empty color,
then one per compatible guard; outgoing occupancy is
max(q_i,d_i-(k_i-1)t_i)<=ceil(4q_i/3). Cases k=2,3,>=4 are elementary.
It extends to branching rooted forests when every outgoing physical
core edge has its own distinct compatible private guard and all guards
reject the parent bundle. This blocks a large rank-cascade lower family.
Do not reinsert the earlier user-removed forest theorem in the paper.

Agent briefly proposed a finite bp=2, chi=3 example as a 3/2 candidate;
root immediately corrected it: scaling gives chi=ceil(5m/2), bp=2m,
so its asymptotic ratio is 5/4. Agent acknowledged and corrected.

Two-core rank-transition polar diagnostics (numerical, not certificates):
2->3 has three threshold cells with gauges 5/4,5/4,19/15. Higher rank
jumps through 12 stayed 5/4 in tested cells. Stop extending these grids.
Shared full-burst heavy blockers at a port force 1/k1+1/k2>=1, so two
ranks>=2 can merge only at rank2/rank2. Naive cyclic rank resets either
fail copy conservation or lose the directional guard incompatibility.

## Exact failed shortcut and numerical diagnostics

`two_star_zero_covariance_exact_obstruction.md` gives a rational joint
law with EX=EY=4/3, variances16/27, covariance0, support[0,16/3], yet
E[1/max(1,X,Y)]=11093/20412<9/16. Support/probabilities:
(0,0):392/3969; (5/6,2),(2,5/6):64/147 each;
(36/11,36/11):121/3969. Positive probe y=.01 also fails after scaling
X,Y by.99. This disproves only a moment relaxation; actual star variables
are independent. Adding bidegree-(2,2) identities numerically still
fails. Script `two_star_joint_moment_probe.py`; root sessions97807 and
62091 are finished/closed.

K=3 expected-max route: means/variances fail, but actual Bernoulli sums
remain plausible. Convex order forces competitor probabilities to their
minimum (1+3a)/4, and endpoint slack is worst when D=probe+competitors.
Reduced exact-star searches found positive margins; not a proof.

Capped 4/5 LP evidence: cap4y appears feasible for binary paired guards,
categorical matched-pair guards, and unit-heavy arbitrary bip support
in small random tests. All allow freely chosen correlations. No theorem.
A common global 1/5 all-free event is NOT w.l.o.g. for capped flow:
many tiny guarded leaves at a free center require staggered free times.
Relevant scripts `paired_capped_45_lp_search.py`,
`paired_categorical_capped_45_lp_search.py`, `unit_heavy_cap4_lp_search.py`.

## Further directions / remaining gaps

* Extend uncapped 4/5 beyond equal weights at saturated heavy vertices,
  or unheavy-center fluid stars. Laminar quota balancing may help if
  fluid bottleneck sets can be uncrossed into manageable laminar sets.
* Prove arbitrary-support unit-heavy cap smoothing, even with a finite
  K(alpha) larger than4. Circle method needs contiguous busy support;
  arbitrary bip matching schedules need not have it.
* General stable-forest DP may expose additive threshold-mass rows for
  weak branches. Fixed-profit message slopes are bounded after local
  normalization; q-independent mixtures and arbitrary profit scales
  remain obstacles. Do not invoke nonlinear HS without proof.
* No new asymptotic physical lower bound above4/3 or3/2 has emerged.
* Recent sparse coverage discrepancy paper arXiv2602.09948v2 retains
  log(graph size) in its general bound; its large-set LLL case does not
  directly close the nonlinear palette gap. Dirichlet rounding paper
  ICALP2026.107 was read but no closing theorem imported.

Live agents at this checkpoint: `extend_paired_fluid_forest`,
`five_hour_physical_rounding`, `bipartite_lower_new_mechanism`. All root
computations finished. Continue substantive research; no proof claim
before the clock/counter thresholds, and no claim after them unless
the actual stated scope has been verified.
