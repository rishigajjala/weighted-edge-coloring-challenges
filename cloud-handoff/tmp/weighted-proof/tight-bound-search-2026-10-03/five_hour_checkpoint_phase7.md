# Research checkpoint, phase 7

4 October 2026. The user last requested an update. That request was
answered in commentary and research continued; it did not cancel the
active tight-bound goal. Do not mark that goal complete or blocked.

## Research time

Fresh exploration began 3 October at 05:21:17 UTC and goal active-time
18,069 s. The user required at least five hours before a proof claim.
Both tests have now passed: at the actual 4 October 08:46:58 UTC check,
the goal counter was 36,946 s, exceeding the 36,069 s threshold. Do not
confuse the overnight wall-clock gap with active research. No idle wait
was used to meet the threshold. This establishes elapsed exploration,
not correctness of a theorem.

## Unrestricted status

No improved unrestricted upper or lower bound. Established manuscript
intervals remain bipartite [4/3,1.62] and general [3/2,1.999]. No manuscript,
Lean, Git, or compiled-document changes were made during this phase.

## Audited physical bridge from phase 6

The root, physical agent, and two independent agents checked
`sparsify_localize_type_palette_bridge_candidate.md` and
`sampled_neighborhood_finite_label_candidate.md`. No gap found at the
stated scope: bipartite combined graph, heavy (>1/2) simple support a
matching, all other physical weights <= sufficiently small tau. The
candidate count is (4/3+epsilon) bp + O_epsilon(1), uniform in graph order,
multiplicity, and minimum positive tiny weight. This remains a scoped
result, not the unrestricted bound.

Audit corrections already incorporated: temporary term caps are12y^k,
averaged caps12tildeY; choose finite field from an a priori type-count
bound before choosing M; averaging sampled supports occurs WITHIN each
color. The Y-tree collision union bound needs no additional radius factor.
The independent audit filename was overwritten concurrently by two
agents, but its current content agrees with both audits. Use unique
filenames for new notes.

## New capped arbitrary-heavy-support result at common weight

Read `common_weight_heavy_dependent_rounding_capped_candidate.md` and
`common_weight_capped_pipage_independent_audit.md`.

The combined graph is bipartite. Each connected heavy component may be
arbitrarily large and has one common heavy weight; different components
may have different weights. For heavy fractional matching target x and
fluid target y with local loads <=1, caps C>=12y, there is a matching
law and capped residual flow with means (.75x,.75y). It is a fractional
one-color theorem, not yet an unrestricted physical-palette theorem.

Proof: capped fluid recourse as a function of active vertices has
nonpositive same-shore and nonnegative opposite-shore cross differences.
The flow-exchange proof preserves caps. Its multilinear independent-
activation extension Phi is convex along every heavy alternating-path
rounding direction: same-shore endpoints move oppositely, opposite-shore
endpoints together. Heavy cycles leave vertex degrees fixed. Starting
z=.75x gives p=.25+.75D. A q-independent martingale rounding law ends
at a heavy matching with E Phi >= initial Phi. Residual concavity and
the capped activation theorem imply E F_q(R,C)>=.75 q.y. Separation
supplies simultaneous means. Both physical and forest agents audited
the argument, including same-shore capped exchange.

## Bounded-component physical transfer

Read `bounded_heavy_component_transfer_interface.md`, written by the
physical agent and read by root. The sparse-label bridge only needs
bounded independent heavy state components, not pairs specifically.
For component size <=h, the interaction row bound becomes h/a and the
finite menu is bounded in h and the heavy bucket count.

For pruning, scale BOTH heavy x and sampled tiny Y by1/(1+eta). The
new residual bound is (D+eta)/(1+eta); the resulting O(eta) heavy stock
loss goes to separate heavy-only colors. Floor probabilities of complete
nonempty matching states to multiples1/q and move removed mass to empty.
This gives coordinatewise larger residuals and exact physical stock,
with O_h(eta N+M/q) leftover heavy degree. The common-weight capped
theorem therefore appears to give the physical4/3+epsilon bound for
bounded heavy components as well. Unbounded heavy components have an
unbounded state menu and still need a local realization.

## Shared weight-profile extension, currently being written

The physical agent independently audited a further extension proposed
by root. Within each heavy connected component, every endpoint-pair
bundle has the SAME conditional weight distribution lambda, while
total occurrence x_uv can differ: x_uv,b=x_uv lambda_b. Round aggregate
heavy matching probabilities. For covered vertices independently draw
W~lambda, yielding residual1-W, and let uncovered residual1. The
expected capped recourse has the same signed cross differences. Its
multilinear extension is again convex along alternating paths. The
initial independent categorical law dominates the Bernoulli law with
the same mean by coordinatewise concavity. At the final matching,
correlate each selected edge's two endpoint weights to one shared W;
opposite-shore supermodularity improves expected recourse. This gives
capped3/4 for shared profiles, still not arbitrary unequal profiles.

Real-capacity cross inequalities have a partial-flow-swap proof. Same
shore: start f(high,high),g(low,low); transfer only
delta=(f_v-cap_v_low)_+ from red to blue along difference-flow source
paths from v. A path ending at u is safe because then g_u>f_u and
g_u<=cap_u_low. All edge amounts remain between old values. Opposite
shore: start f(highu,lowv),g(lowu,highv) and transfer the analogous
blue excess from v to red. This proves the continuous signed cross
inequality without cloning. Await the physical agent's detailed note.

## Exact heterogeneous rounding obstruction

Read `heterogeneous_pipage_chord_exact_obstruction.md`.
H path0-1-2-3-4, x=(1/3,2/3,1/3,2/3), weights(1,.5,w2,1), w2 in[.5,1].
Fluid chord1-4 has target y=1/3 and cap>=4 (effective cap1). At alpha.75,
initial independent activation p1=p4=.5 givesPhi=.25, exactly target.
An alternating path step (+,-,+,-) yields branch(.75,0,.75,0) with
prob1/3 and branch(0,.75,0,.75) withprob2/3. Rounding remaining disjoint
fractional edges independently gives actual mean chord recourse
(1/3)(1/4)+(2/3)(5/32)=3/16 <1/4. Thus generic pipage fails even for
one fluid edge with unequal heavy weights. Correlating each branch's
remaining heavy edges together gives full matchings with masses.25,.5
and empty.25, restoring exactly1/4. This is a rounding-rule obstruction,
not a hull counterexample. The fix comes from extra correlation, not
from Jensen slack between real and binary residuals.

Two exactly tight endpoint chords on an odd heavy path were also tested:
they align with the same global empty state, so no simultaneous conflict
was found. On an even path, both opposite-uncovered endpoints cannot
each have D=1/3 because their matching probabilities cannot both be>=2/3.

## General nonbipartite capped obstruction

`general_matching_heavy_capped_global_coin_obstruction.md` gives a diffuse
star showing full-heavy law plus one global empty coin fails with caps.
m leaves, disjoint unit guards x_i=1-1/m, tiny y_i=1/m, caps12/m, m>24.
Any full-heavy law supplies total expected capped flow<=12/m. Mixing
it with probability2/3 and empty with1/3 gives<=1/3+8/m<2/3. The target
already is a forest extreme, so cap-concavity decomposition does not
repair this. This does not refute existence of a better scaled law.
Conversely the minimal two-spoke odd core is repaired by positively
correlated guard absences. A successful general law must combine
diffuse spreading with local positive correlations.

## Lower-bound search

No new asymptotic lower construction. Lower agent tested rank2/rank3
alternating count-state reversals, allowing a guard to accept one large
outgoing item but reject two smaller incoming ones. Two targeted exact-
pattern / floating-polar searches had maxima5/4 and7/6, each dropping
one intended rank in the optimizing profit. These are diagnostics, not
new rational lower-bound certificates. Agent is exploring nonpath
factor interactions next.

## Agents and next work

Physical agent: shared-profile proof note and modular transfer audit.
Forest agent: exact heterogeneous obstruction saved; competing chords.
Lower agent: nonpath mixed-rank interactions.
No root subprocess runs. Use agents aggressively, avoid repeating old
scalar reciprocal-policy searches, and keep unrestricted claims separate
from all scoped fractional and physical statements.
