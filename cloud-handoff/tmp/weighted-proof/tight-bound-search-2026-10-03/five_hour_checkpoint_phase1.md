# Five-hour exploration: first phase checkpoint

User instruction: explore for at least five hours before claiming a new proof.
See `five_hour_research_protocol.md`. Start: 2026-10-03 05:21:17 UTC.
Earliest wall-clock claim: 10:21:17 UTC, also requiring active-goal work-time
counter >=36,069 seconds. At 05:50:31 UTC the counter was 19,829 seconds,
so only about 29 minutes of the newly requested exploration had elapsed.
The active tight-bound goal remains active. No unrestricted bound changed,
and no paper or Lean repository file was edited.

## Important candidate progress

1. The independent vertex-activation argument now has a finite-edge-cap
   extension. With p_v=1/4+3D_v/4 and target Ay<=D, edge caps C>=12y,
   the candidate inequality is E F_q(1_A,C)>=3q.y/4. On forests the leaf
   insertion uses cap min(C_e,1) and concavity in the neighbor's capacity.
   For arbitrary bipartite support, decompose the target into forest
   extremes of the UNBOUNDED degree polytope, vary each temporary cap as
   12 times that extreme, and use concavity in edge caps to average back.
   Thus the individual forest components need not respect the same cap.

2. Capped bipartite recourse is supermodular between opposite-side active
   vertices and submodular between same-side vertices. The directed
   difference-flow path exchange preserves every physical edge cap.
   A bipartite double cover consequently extends the independent-vertex
   activation candidate to all loopless graphs. This does NOT extend the
   independent heavy-pair law to general graphs; its exact old counterexample
   remains valid.

3. These candidates transfer to categorical heavy matching support in
   a bipartite combined graph with genuine finite tiny-edge supplies.
   Heavy weight inflation provides absolute tiny-rounding slack. The
   bipartite per-pattern rounding loses at most tau, giving a candidate
   FRACTIONAL physical factor 4/[3(1-tau)] for N>=12 and heavy-matching
   support. The integer finite-palette statement remains unresolved.

4. A further quantitative property: choose the minimal cap C=12y rather
   than the full physical stock. For y_e=w_e/N this bounds every conditional
   tiny-edge inclusion fraction by 12/N (up to the harmless slack scaling),
   even after conditioning on the complete heavy state. This may be the
   missing input for uniform profile/finite-palette rounding. Smallness
   alone does not justify swapping expectation and simultaneous feasibility.

5. Root and heavy-support agent found a candidate arbitrary-heavy-support
   BIPARTITE transfer when all heavy weights share one value w. Round
   alpha*x by unbiased alternating-path/cycle pipage. After complementing
   right-side activation bits, capped recourse is submodular; its multilinear
   extension is convex along each endpoint swap. Common w preserves the
   internal weighted degrees. At a final heavy matching, joint concavity
   in capacities dominates independent binary activation at the residual
   means. This gives the 3/4 fractional inclusion in this restricted weight
   case. Unequal heavy weights change internal capacities during a path
   move, so this does not prove the unrestricted statement.

The capped argument received independent checks from both the physical-
rounding and heavy-support agents, and the root audited its formulas. All
remain research candidates during the requested minimum exploration period.

## Saved detailed notes and computations

- `five_hour_capped_activation_audit.md`: root's complete proof audit,
  precise scope, and cap-constant sharpness (K>=12 is necessary for the
  proposed activation law on one edge as its target tends to zero).
- `physical_tiny_cap_rounding_route.md`: full capped proof, physical slack
  transform, small conditional fractions, integer palette criterion and gap.
- `heavy_forest_bipartite_activation_candidate.md`: same/opposite-side
  recourse inequalities, star blocker law, unit blocker pipage, and weighted
  lifting obstruction. Agent is saving the common-heavy-weight extension.
- `five_hour_capped_activation_probe.py/.log/.json`: 1,200 completed
  floating-point tests; no K=12 or K=16 violation. K=4,8 do fail. Session
  18677 was polled to completion (exit0); no root computation is live.

## Exact finite-palette obstacle

For a fixed heavy schedule H in M colors, let R^c(H) be its residual
capacities. The tiny fractional assignment with exact edge stocks exists
iff for EVERY q>=0,

    sum_c F_q(R^c(H), C=w) >= sum_e q_e w_e.

The one-color law establishes only averaged support inequalities over
heavy schedules. There is a small physical example at N=M=4 where a mixture
of schedules supplies every tiny stock in expectation but no one four-color
schedule works. Two heavy pairs each have two unit-heavy edges. The tiny
bundles are p_L-q_R of weight1.1, c_L-p_R of weight1.3, and c_L-q_R of
weight0.8. If the two size-two free palettes overlap in <=1 color, the first
bundle fails; if overlap is two, the hub's load2.1 fails. A mixture of flow
tables has fractional cost4, while integer cost5. Arbitrarily tiny uniform
physical edges realize all the bundle weights. This is an additive gap at
small N, not a counterexample to the prospective 4N/3 asymptotic palette.

## Lower-bound branch

No stronger lower bound emerged. Paired-heavy/divisible-fluid K3,3 and
K4,4 templates, several shared-port frustration gadgets, physical rank-two/
rank-three versions, and small nonbipartite substitutions repeatedly reduced
to existing 5/4 path or 3/2 triangle subpatterns. These are finite-template
diagnostics only.

Useful barriers are saved or being saved by the lower-bound agent:

- `paired_fluid_relation_port_parity_barrier.md`: a cyclic system of direct
  edge / shared-star correlation gadgets with distinct ports at every blocker
  has even negative-relation parity. Genuine frustration must reuse a port,
  creating local competition that simple templates do not overcome.
- Any multigraph on only three vertices has local-to-global configuration
  gap at most3/2 for arbitrary weights: choose a vertex uniformly and sample
  its local bin; each edge is included through two of its three centers.
  Thus a larger lower bound needs essential interaction on >=4 vertices.

## Running work and next directions

Agents remain assigned to: (a) heterogeneous heavy support / martingale
lifting; (b) finite-palette transfer using small conditional edge fractions;
(c) larger interacting lower-bound gadgets, including boundary-response
substitutions. Root should continue substantive research, not wait for the
five-hour clock. Keep all candidate claims out of the main manuscript and
private Lean repo. Do not revisit the completed repository cleanup.
