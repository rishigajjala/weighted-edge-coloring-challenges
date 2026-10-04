# Shared-blocker mixed-rank factor diagnostic

Status: finite physical-color calculations and a scoped structural barrier.
None of the calculations changes the unrestricted bipartite lower bound.

## Factor-law coherence gives at most 5/4

Suppose disjoint factor gadgets meet only through blocker edges, the
blockers form a matching on their port vertices, and a proposed local
point actually supplies a joint feasible law for each *whole factor*
(including each incident blocker state). Let `S` be the expected total
internal-factor profit, `q_e≥0` the blocker profit, and `p_e` the common
marginal probability of blocker `e` at its two ends. Put

    A = sum_e q_e p_e,  B = sum_e q_e p_e^2,  P = sum_e q_e.

The local objective is `L=S+A`. Independently sampling the factor laws
and retaining a blocker exactly when both factors request it is a
feasible physical color with expected profit `S+B`. Selecting all
blockers is also feasible and has profit `P`. By Cauchy,
`B≥A²/P` (with the zero-profit case handled directly), so

    L/M ≤ (S+A)/max(S+A²/P, P) ≤ 5/4.

For the second inequality, normalize `p=A/P` and `r=S/P`. At fixed
`p∈[0,1]`, `(r+p)/max(r+p²,1)` is largest at `r=1−p²`, where its value
is `1+p−p²≤5/4`. Thus frustrating factor *phases* connected only by
matching blockers cannot produce a larger lower bound. The original
vertex-local LP need not yield whole-factor laws; this hypothesis is
essential. Overlapping blockers also invalidate the all-blockers
physical color.

## Fixed three-phase laws

`three_phase_shared_blocker_probe.py` examined four bipartite factors,
each a star with spoke groups of weights `(1)`, `(1/2,1/2)`, and
`(1/3,1/3,1/3)`, and one unit blocker per port. The target law mixes
the three full-bin groups equally, making each blocker marginal `2/3`.
For uniform blocker profit, simply choose the one-spoke group in every
factor and every blocker not touching it: there are `3n` blocker edges,
at most `n` are excluded, and the result meets/exceeds the target
`2n` blocker count with the same spoke profit. Optimizing all blocker
profits over 100 four-factor bipartite matchings gave at most `19/18`.
With mixed spoke groups `(.60,.40)`, `(.55,.45)`, and
`(.34,.33,.33)`, `three_phase_rank_mixture_probe.py` found at most
`1.055635` over 100 matching topologies. These finite findings are
subsumed conceptually by the factor-law `5/4` barrier.

## Factor-incoherent count law

A more relevant factor has three spoke bundles of capacities 2,3,3.
The hub-local law takes one spoke from each bundle per color; each port
locally explains that spoke marginal with a full-burst alternative and
a unit blocker. Thus the blocker marginal is `1/2` at the rank-two
port and `2/3` at each rank-three port. There is no joint factor law:
the hub wants all three ports occupied while the port laws want
blockers during most colors.

`incoherent_three_port_factor_network_probe.py` took four such factors,
one matching blocker per port, weights `(.4,.3,.26)`, and normalized
spoke profits `(.5,1/3,1/3)`. It enumerated all 48 bipartite blocker
matchings compatible with the marginals, all physical blocker subsets,
and the exact hub knapsack recourse, optimizing every nonnegative
blocker profit for this fixed local point by a linear-fractional LP.
The largest numerical ratio was `53/48≈1.10417`. For the changed
weights `(.42,.31,.26)` and profits `(.55,.35,.30)`, the one-each hub
pattern is uniquely profit-optimal; the largest ratio became `1.12`.

`incoherent_three_port_overlap_probe.py` gave every port two unit
blockers; the blocker graph is the union of two bipartite perfect
matchings. Each rank-two blocker has marginal `1/4`, and each
rank-three blocker `1/3`. Across all 48 topologies, optimizing blocker
profits at the last fixed spoke-profit vector gave at most `1.106667`.
Finally, `incoherent_factor_full_profit_lp.py` optimized **all** three
spoke profits and all 12 blocker profits for the same fixed local count
law using physical-color pricing and cutting planes. Its maximum over
the 48 topologies was numerically `9/8`, attained when only rank-two
spokes and their blockers carry profit; the mixed-rank effect vanished.
This is a floating-point finite-template diagnostic, not a universal
certificate or a claim about larger factor networks.

The tested factor-incoherent pattern is too weak by itself. A stronger
construction would need interacting count mismatches across several
nonmatching core bundles, or a hub law whose profitable mixed pattern
cannot be repaired by an alternate count pattern after one port is
blocked.
