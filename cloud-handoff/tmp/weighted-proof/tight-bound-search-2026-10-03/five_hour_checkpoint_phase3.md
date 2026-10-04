# Five-hour exploration: phase-three checkpoint

Written around 2026-10-03 07:09 UTC. The new exploration began 05:21:17 UTC;
minimum proof-claim time remains 10:21:17 UTC and goal time counter >=36,069.
At 07:06:11 UTC the counter was24,369. About105 minutes of the new period had
elapsed. Keep all new results as interim candidates, and continue substantive
work. No manuscript or Lean changes were made.

The previous goal turn was progress: new exact restricted arguments, explicit
counterexamples to proposed shortcuts, and localization removed one conditional
step for a bounded-degree class. The full objective is still tight bounds for
all weighted bipartite/general multigraphs, not merely heavy-plus-fluid models.
Current unrestricted intervals remain [4/3,81/50] and [3/2,1999/1000].

## New bipartite heterogeneous-heavy arguments

All below concern categorical heavy edges forming a matching per color and
uncapped divisible fluid; they do not yet give an unrestricted integer coloring.

1. **Fluid matching support, arbitrary heavy support.** For disjoint fluid pairs
   uv add ordinary matching coordinates
   b_uv=min(1-deg_x(u),1-deg_x(v)) to heavy x. The combined bipartite degree vector
   is feasible and decomposes into ordinary matchings. Forgetting fluid selections
   gives full-heavy law with nested coverage events at each fluid pair,
   simultaneously. For nested-positive-support loads U,V in {0} union[1/2,1],
   putting Z=U-V gives Z_++2Z_-<=1 after orienting the nesting. Therefore the
   Jensen gap Emax(U,V)-max(EU,EV)<=1/3. Mix this full heavy law with an empty
   heavy state in proportions3/4,1/4. This gives desired heavy marginals and
   expected fluid recourse >=3/4 min(D_u,D_v) simultaneously on all disjoint pairs.
   Root and agent independently audited it.
   File: bipartite_fluid_matching_heterogeneous_heavy_transfer.md.

2. **One arbitrary-profit fluid star, heavy center allowed.** Order leaves by
   profit. Add ordinary matching spoke masses b1=min(a_c,a1),
   b2=min(a_c-b1,a2), where a_v=1-deg_x(v). The full-heavy law then nests center
   freedom with leaf1 freedom and with the union of top-two leaves' freedom.
   The top-one recourse has additive gap<=1/3; top-two has gap<=1/2 by a short
   scalar argument. Conditional on the full matching, assign center heavy edge
   and top-one leaf heavy edge phase1, top-two phase2, top-three phase3, retaining
   center-edge identity if it itself joins a leaf. Delete one uniform phase of4.
   Exact mean recourse for top-one is1/4+3F1/4; for top-two it is
   1/4+X/4+F2/2. Prefixes of size>=3 get >=3D_c/4. Layer-cake over profits proves
   the3/4 support bound; separation recovers all fluid marginals.
   Root read and independently audited the saved proof and its case identities.
   File: bipartite_single_fluid_star_heterogeneous_heavy_transfer.md.

3. **A disjoint fluid star forest with heavy-free centers.** Only top-three leaf
   deletion phases need be distinct. Each selected heavy edge constrains at most
   two stars, giving an auxiliary bipartite multigraph of maximum degree3.
   Proper3-edge-coloring plus a fourth deletion phase synchronizes all stars.
   This gives3/4 transfer with arbitrary heterogeneous heavy support. For this
   unheavy-center result heavy weights may lie throughout[0,1].
   File: bipartite_unheavy_center_star_forest_phase_transfer.md.

## True remaining bipartite synchronization problem

For many stars with heavy centers the ordinary matching augmentation can be
done simultaneously, but phase equalities (center-heavy = top-one-leaf-heavy)
can conflict with top-two/top-three distinctions. An explicit self-conflict:
fluid star S has center c_L, top1 a_R, top2 b_R; star T has center x_L, leaf y_R;
selected heavy matching is {b_R x_L, y_R c_L, a_R z_L}. Equalities force all
three heavy colors equal, so S's top-two distinction is impossible. This only
refutes the overly strong phase prescription; for deterministic heavy x the
original fluid target is already feasible.

The equality graph consists of alternating paths/cycles of selected heavy
matching and top-one fluid matching. Tight center-free constraints consume path
endpoints and are sparse; exploiting scalar slack on other constraints may be
possible. A naive rule permitting collisions whenever the center is matched is
false as a scalar statement. Agent has an abstract mixture showing this.
That mixture requires positive correlation of sibling heavy coverage; ordinary
bipartite dependent rounding could rule it out, but it is not known how to
combine same-shore negative correlation with the opposite-shore free-event
nesting produced by auxiliary spokes.

## Local allocation and integer transfer

- The explicit radius-one K=4/3 policy is still unproved. Root's continuous
  adversarial optimization ran54 searches over1+1 through4+4 spoke stars and
  K=4/3,2,3. All converged to ratio>=.75, often the known boundary equality.
  These are numerical tests only.
  Files: two_star_policy_adversarial_optimization.py/.json/.log.
- A bounded-radius policy **does not need that conjecture**. Decompose y into
  forest-supported extremes y^k at fixed D; caps12y^k average to12y. Cut each
  rooted forest at a uniform depth residue modR. Components have diameter<=2R
  and each edge loses1/R of its target. Apply the existing capped paired-heavy
  transfer plus separation separately to each component, then average. This
  gives a q-independent policy of radiusO(R), cap12y, and mean at least
  (3/4)(1-1/R)y. Heavy pairs crossing boundaries cause no issue. Do NOT transfer
  an arbitrary independent-activation policy after correlation; use separation
  under each component's paired law directly.
- This removes the explicit local-rule assumption from the bounded-simple-tiny-
  degree finite-palette bridge: finite graph-power types and a constant-dimensional
  exact-quota seed design approximate every local state law uniformly in graph
  order, then surplus and source-preserving3tau rounding finish the restricted
  integer transfer. File: bounded_degree_capped_localization_audit.md.
- For unbounded degree, agent has a more elaborate **conditional** bridge for
  the explicit radius-one rule: strong/weak sources, finite-field blocks,
  weighted defective sublabels to set aside O(epsilon N) bad tiny stock, and
  blockwise Harris--Srinivasan balancing. It is being audited; it depends on the
  unproved explicit local inequality and several delicate conditioning details.
  File: weighted_defective_palette_bridge_conditional.md.
- The implicit forest policy does not automatically have the weak-load stability
  needed by that bridge. Arbitrary optimal recourse can flip between near-tied
  allocations when a weak bridge changes, so naive Lipschitz selection is false.

## General-graph method counterexample

Independent activation of paired ports with p_P=1/3+(2/3)D_P fails to retain2/3
of arbitrary fluid target. Put two leaves in one pair, center plus isolated vertex
in another. Give each spoke target3/8; D_leafpair=3/8,D_centerpair=3/4. Expected
unit-profit recourse is(7/12)(5/6)=35/72, below target1/2=36/72.

For general alpha and spoke target t, the deficit polynomial is
(1-alpha)^2+alpha(1-3alpha)t+2alpha^2 t^2.
Its minimum is(7-10alpha-alpha^2)/8, so this independent-pair method cannot exceed
alpha=4sqrt(2)-5, inverse factor(4sqrt(2)+5)/7≈1.522408. Positive correlation
repairs this particular star; a globally common threshold harms multi-leaf stars.
This is a method barrier, not a coloring lower bound.
File: general_paired_activation_two_leaf_counterexample.md.

Root's earlier5,000 random general-activation tests missed this narrow family;
the exact example was checked separately by LP. Random passing tests have no
proof status. Session38464 and session74903 are both completed and closed; no
root computation remains live.

## Lower-bound work

No improvement over4/3 or3/2. The lower-bound agent obtained a scoped3/2 upper
barrier for an entire matching-linked network of triangle factors (unit direct
edge, two divisible spokes, private hub), including unequal blocker weights and
arbitrary asymmetric profits. Root checked the five-ray argument; a typo and
the same-blocker-on-both-ports case were sent back for correction. Agent is
extending it to single discrete spokes; parallel bundles and more complex
multi-port factors remain outside the proof.
File: asymmetric_triangle_factor_network_three_halves.md.

## Live agents

- extend_paired_fluid_forest: synchronize heavy-center stars / general fluid
  forests; investigate joint nesting and same-shore coverage correlation.
- five_hour_physical_rounding: explicit local inequality, arbitrary-degree
  palette bridge audit, stability/localization alternatives.
- bipartite_lower_new_mechanism: higher-rank or multi-port correlation gadgets,
  beyond triangle-factor mechanisms now ruled out.

Continue toward the unrestricted goal. The restricted results do not close it.
