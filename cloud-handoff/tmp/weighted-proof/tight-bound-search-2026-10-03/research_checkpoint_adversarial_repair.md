# Checkpoint: arbitrary tiny support and adversarial matching-law repair

The full tight-bound goal remains active and unsolved. The proved unrestricted
asymptotic intervals remain

* `4/3 <= c_bip <= 81/50`;
* `3/2 <= c_general <= 1999/1000`.

No manuscript theorem or Lean proof was changed in this research turn.
The preceding user-requested repository cleanup was completed and pushed at
`65856c8e27e48efc51b429719e075f097a08e119`; it changed comments only.
That cleanup was not a mathematical improvement. This research turn is
**progress**: a new arbitrary-support tiny-edge lemma was proved and checked,
two proposed transfer steps were refuted exactly, and a stronger numerical
repair test materially sharpened the next proof target. None closes the
unrestricted gap.

## Positive statements checked

The saved source-permutation theorem in
`arbitrary_linked_stars_real_integer_transport.md` is valid. For shared
two-hub state lists with coordinates in `[0,1]`, private lists of range at
most two, and hub mean at most one, it gives simultaneous overload
`N/2 + 6 popcount(N)`, and exactly `N/2` for powers of two. Its physical
transfer still requires heavy simple support to be a matching and tiny
simple support to be a vertex-disjoint star forest.

`arbitrary_tiny_support_repair_audit.md` now proves, for every loopless
multigraph whose edge weights are at most `tau<1/14`,

`chi'_w <= ceil(Delta_w/(1-14 tau))`.

The proof gives a coloring into any `M>=1` colors with vertex/color load
at most `Delta_w(v)/M + 14 tau`. It uses two-sparse signing, exact source
quotas, and common dyadic color blocks. The root checked both the floating
constraint count and the error recurrence. The bound is independent of
graph order and multiplicity. This is a tool for coloring a small-edge
repair graph, not a solution for mixed edge weights.

The same note records the extreme-support reduction for the original
heavy-matching/divisible-fluid local LP. After putting `t_e=w_e x_e`, it
has unsigned incidence constraints `A t<=1` and heavy boxes `t_e<=w_e`.
At a vertex of this polytope, the positive coordinates not at an upper
bound have linearly independent columns on tight vertex rows. Their
support components are trees or odd unicyclic graphs. The positive
upper-bound heavy edges form a matching. Exploiting the links between
these components remains open.

## Exact failures of naive extension

The tiny-edge note has two explicit star examples; both graphs themselves
are `N`-colorable.

1. A normal placement can have zero overload at a hub while deleting tiny
   edges to repair its neighbors forces deleted weighted degree `N` at
   that hub. Thus per-vertex overload at most `N/2` does not bound the
   degree of the union of deleted edges by `N/2`.
2. Giving all heavy pairs the same nested prefix of colors can force
   nearly `2N` colors, although dispersing their free colors gives `N`.

Do not combine the source-overload theorem with the tiny-edge packing
lemma without a new argument controlling deletion union degrees, and do
not try globally nested heavy color subsets again.

A secondary moment calculation initially claimed each neighboring heavy
pair contributed at most `3/4`. The root found the error: a vertex can
send tiny edges to both endpoints of that pair. The corrected bound is
`18-12 sqrt(2)>1`; `3/4` holds only for one neighboring vertex. The agent
corrected the note. These moment bounds are not a coloring construction.

## Stronger numerical test of global fluid repair

`adversarial_projected_law_probe.py` and its `.log` are completed.
Session `61801` returned exit code zero. No root computation remains live.

For 1,500 random instances on five to eight vertices, the script finds a
locally feasible heavy/fluid extreme point, fixes heavy means at `2/3`,
and maximizes retained unit-fluid mass over laws on ordinary matchings.
There were **496 nontrivial projections** with fluid removed. For each,
five fluid-profit directions were tested (all ones and four random
nonnegative integer vectors).

For each direction, the script computes the optimal divisible-fluid value
in every heavy state, then **minimizes** its expectation over every law
that preserves the heavy means, respects the fluid upper bounds, and
retains the maximum total unit-fluid mass. In all 2,480 tested directions,
even this adverse law met the target `2/3 q.y`. All unit fluid was released
globally before reoptimization.

This is floating-point, nonexhaustive evidence only. It is stronger than
the previous 5,000 arbitrary-law probes, but does not prove any universal
inequality or existence theorem. A useful next target is whether every
maximum-total projection law admits full global fluid repair, allowing
all fluid to move. Failure of that stronger claim would still leave the
existential mixed-model theorem open.

## Exact analytic repair targets

`transfer_one_blossom_reoptimization_lp.md` includes the exact joint-law
minimax criterion, factor-critical positive support, a lexicographically
acyclic fluid exchange relation, and two further identities:

* Statewise fluid vertex-cover duals express the global repair deficit as
  a weighted covariance term, with a one-third average-price allowance.
* For unit fluid profits, fractional vertex-cover half-integrality gives
  `F_1(r) = (sum_v r_v - max_I [r(I)-r(N(I))])/2`, with `I` independent
  in the fluid support.

Neither proves the required inequality. In particular one cannot
interchange the maximum over independent sets with expectation.
Heavy weights may equal one: any residual insertion has size `1-w_e`,
which may be zero. The agent corrected the strict positivity claim and
added the exact covariance identity with its nonnegative slack terms.
All three agents have saved their notes and concluded this research turn.

## Bipartite lower-bound work

`bipartite_shared_factor_parity_barrier.md` proves that the equal-profit
edge-count certificate cannot exceed `4/3` for arbitrary locally pairable
heavy/medium 2-factor gadgets. Independent alternating choices violate
at most one quarter of the threshold compatibility constraints on average.
This does not settle unequal-profit certificates or chromatic upper bounds.

An inherited-weight graph lift cannot amplify its base instance's ratio:
every base coloring lifts with the same palette and the local stars are
unchanged. A targeted polar oracle reproduced `7/6` for the base K4,4
example, one twisted lift, and one small perturbation. These tests establish
no new lower bound.

## Literature checked

Goemans--Pan, arXiv:2609.17932, studies the intersection of local knapsack
polytopes for demand matching and gives approximation bounds for a broader
nonuniform-capacity model. Its stated bounds do not improve the bounds
above. One-copy/nonuniform-capacity lower bounds cannot be transferred to
our repeatable-type, common-capacity model without a proof.
Source: https://arxiv.org/html/2609.17932v1

Next proof effort should address the joint repair inequality or the
extreme-support component coupling, rather than tuning a weight cutoff
or repeating stationary lower-bound templates.
