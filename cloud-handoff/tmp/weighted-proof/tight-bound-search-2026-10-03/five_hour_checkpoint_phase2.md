# Five-hour exploration: phase-two checkpoint

Checkpoint written approximately 2026-10-03 06:32 UTC.

The new exploration began 05:21:17 UTC. Minimum new-claim time remains
10:21:17 UTC, also requiring goal timeUsedSeconds >= 36,069. At 06:30:57 UTC
the counter was 22,255. Only about 70 minutes of the new exploration have
elapsed. No unrestricted result has been proved or claimed. No manuscript or
Lean repository edits were made.

The active goal remains tight bounds for bipartite and general multigraphs.
Current unrestricted intervals remain [4/3,81/50] and [3/2,1999/1000].

## New progress

1. A candidate radius-one capped fluid policy could resolve the nonlocal-policy
   difficulty in the finite-palette argument. It uses
   b_e=min{(4/3)y_e/(p_up_v),12y_e}, then divides each activated edge by
   max{1,L_u,L_v}. Feasibility is immediate, but E z_e >= 3y_e/4 is **unproved**.
   Extensive random tests passed; these are not a proof. Conditional on the
   probe endpoints activating, the two competitor sums are independent, so the
   missing inequality is a purely two-star probability statement.
2. Root and the physical-rounding agent derived an explicit reservation that
   removes internal tiny bundles from each heavy pair. It preserves their
   desired expected flow and caps, leaving a paired residual with the same
   affine activation formula for the external targets. This makes the local
   policy's favorable pair-correlation comparison applicable externally.
3. A simple Jensen bound on the expected denominator is false for K=4/3 and
   also narrowly false for K=2 (three-spoke versus four-spoke centers). The
   expected-reciprocal policy itself is not refuted. Root derived a short
   one-sided leaf-edge Jensen inequality in the self-load-at-least-one regime.
4. Assuming a local policy, fixed-edge concentration under exact heavy
   injections has graph-order-independent exp(-c epsilon^2 N) tails using
   weighted sensitivities. A simultaneous graph-order-independent argument is
   still missing; a union bound is insufficient for the intended uniform bound.
5. The proposed shortcut C_q(x)>=F_q(D)-F_q(1)/3 is false on a heavy C10 with
   alternating weights3/5 and1 and a five-leaf fluid star. Full heavy marginals
   force two perfect-match states and give recourse1/2 versus F(D)=F(1)=1.
   At scaled marginals3/8, a partial-matching law has recourse1 in every state,
   so this only refutes the shortcut.
6. The heterogeneous q-specific dual is now explicit: W_q(a) is the concave
   closure of matching recourse, with affine-majorant dual. Alternating
   recombinations preserve edge marginals. The fluid target can be decomposed
   into forest-supported extremes at the same heavy x,D, so it suffices to
   solve fluid forests (heavy support arbitrary). This is a reduction, not a
   proof of the target.
7. Exact analysis of the sparse C6 one-chord family gives
   W_q(alpha x)=(1-alpha)(2-h) for alpha in[2/3,1], far above the target at3/4.
   The stronger independent mean-activation domination does fail at alpha1.

## Principal files

- phase2_local_policy_and_additive_gap_audit.md — root's exact reductions,
  sharp cases, and false shortcuts.
- heavy_forest_bipartite_activation_candidate.md — common-weight candidate,
  heterogeneous dual, fluid-forest reduction, false additive-gap route corrected.
- bipartite_heavy_c6_one_chord_exact_recourse.md — exact primal/dual witness.
- physical_tiny_cap_rounding_route.md and finite_palette_capped_transfer_audit.md
  — previous phase's capped theorem and quantifier gaps.
- bounded_heavy_pairs_integer_transfer_candidate.md — restricted fixed-H result.
- triangle_substitution_and_four_vertex_checkpoint.md — lower-bound diagnostics.

## Lower-bound status

No improvement over4/3 bipartite or3/2 general. New finite tests on K5 and mixed
parallel extensions still optimized on triangles. All-real-profit nonconvex
solver runs were numerical with tolerances, not exact upper certificates.
A narrow C5 template gives79/63>5/4, useful only to disprove a simplistic cycle
subdivision hypothesis, well below3/2. The agent has stopped repetitive small
template sweeps and is pursuing higher-rank/scalable junction mechanisms.

## Agents and next work

- extend_paired_fluid_forest: q-specific heterogeneous matching/recourse law,
  fluid-star and forest route; arbitrary thinning and additive-gap shortcuts
  have explicit counterexamples.
- five_hour_physical_rounding: prove or refute the two-star local inequality,
  then uniform simultaneous finite-palette concentration. It is saving scripts
  previously in /private/tmp into the research directory.
- bipartite_lower_new_mechanism: new higher-rank and scalable correlation gadgets.

The 5,000-instance heterogeneous recourse probe completed with no sampled
alpha3/4 violation; terminal2835 was closed. No root computation is left live.
Continue substantive exploration, not waiting to fill the five hours.
