# Five-hour exploration checkpoint, phase 6

3 October 2026, roughly 11:45 UTC. Research continues; do not end the task
because another 40-minute block has elapsed. The user's latest `update`
was answered in commentary; it did not cancel the active goal.

## Time and goal

Fresh exploration began 05:21:17 UTC, with goal active-time counter 18,069s.
The user's five-hour requirement is satisfied only when BOTH wall time is
after 10:21:17 UTC AND active-time counter is at least 36,069s. A long pause
means wall time alone is insufficient. Last actual read at 11:37:46 UTC:
active counter 33,911s, still roughly 36 minutes short. Recheck before any
new proof claim. Do not idle to fill time.

Unrestricted established manuscript intervals remain bipartite [4/3,1.62]
and general [3/2,1.999]. No manuscript, Lean, or Git changes this phase.

## Most important new progress: possible uniform physical bridge

Read these FIRST on continuation:

- `sampled_neighborhood_finite_label_candidate.md` (root-written; independently
  checked by both lower-bound and forest agents, including primary HS input).
- `sparsify_localize_type_palette_bridge_candidate.md` (physical agent's
  full assembled candidate; root read it and found no substantive gap so far;
  final independent audits still running).
- `bounded_degree_capped_localization_audit.md` and
  `physical_tiny_cap_rounding_route.md` are existing foundations, re-audited
  by forest agent during this phase.

Intended scope: combined graph BIPARTITE, simple support of heavy edges
is a MATCHING (arbitrary parallel heavy types/weights>1/2), all other
physical weights <=tau. Candidate colors `(4/3+epsilon)N+O_epsilon(1)`
for tau sufficiently small and N=bp sufficiently large, UNIFORM in graph
order, multiplicity, and smallest positive tiny weight. This would bypass
the unresolved radius-one reciprocal policy. It is NOT unrestricted.

### Core new idea

Independently sparsify normalized tiny bundle target y: retain strong
y_e>=a deterministically, sample weak e with probability y_e/a at target a.
Prune edges touching vertices with sampled load>D+eta, then divide all
targets by 1+eta. Conditional-on-e Bernstein yields E y^S_e >=
(1-delta_pr)y_e/(1+eta); retained simple degree is O(1/a).

For each fixed S, decompose target into uncapped degree-polytope forest
extremes, cut one depth residue modulo J, and use existing capped activation
theorem on the bounded components. The component policy is q-independent,
feasible, capped at12y^S, and depends on <=B(a,J) heavy-pair state IDs in a
sampled ball of radius r=2J+2.

Actual pair residual R has mean p_act>=.25+.75D. Sample shared A|R~Bern(R)
and couple to A' with p'=.25+.75(D+eta)/(1+eta). If p_act<p', augment; if
larger, thin. Augmentation-only probability<=.75eta. Use local capped flow
under A', zero edges unless both actual A endpoint bits are1, then condition
away all auxiliary bits. This is feasible pointwise under R and loses at
most18eta*y^S_e in mean, by the cap. Thus support-averaged baseline mean
is beta0*y_e with beta0 arbitrarily close to .75.

### Finite-label lemma

On contracted heavy pairs, unpruned sampled edges have independent
unordered-pair indicators and probability bound matrix T symmetric with
row sum<=K=2/a. Let W=I+T+...+T^r and S0=sum K^ell. Both row and column
sums<=S0. Strong entries W_jA>gamma define bounded-degree graph; square
color it, so strongly reachable distinct vertices at each j have distinct
base labels. Choose Q sublabels using Harris--Srinivasan on weak weighted
rows (j,base,sub). After scaling by gamma, row means<=S0/(Q gamma), source
column sums<=S0/gamma, independent of base-label count and graph order.
Pick Q then gamma small to get every weak final-label load<=xi.

Then C_j=sum_{A!=B,same final type}W_jA W_jB<=2xi S0. A bad sampled rooted
r-ball has a BFS Y-tree witness with three edge-disjoint arms (zero lengths
allowed). Independence applies BEFORE replacing path sums by all walk sums,
giving Pr[bad ball atv]<=sum_jW_vj C_j<=2xi S0^2, uniformly in v. Pruning
only deletes edges. The lemma was independently checked by two agents;
lower agent also checked primary HS Theorem4.7, arxiv1406.5943v5.

Drop local component terms with repeated types. A rare edge conditional
collision probability need NOT be small. Instead aggregate lost marginal
at each physical port is <=12delta_col (indeed feasibility may give
delta_col, but the proof uses the safe12 bound). Mark bundles losing more
than theta*y_e; marked original stock at each vertex is O(delta_col/theta)N.

### Exact physical palette

Average all S/component/auxiliary policies WITHIN EACH COLOR. Sampling just
one S per color fails for arbitrarily tiny y_e. Averaging yields physical
relative cap12 E y^S_e<=12y_e and per-color feasibility.

Use an a priori finite type-count bound (depends only constants), choose
prime-power q above it and q>=3K_b/epsilon_heavy, let field block length
L=q^B, then choose M=L ceil((1+rho)N/(beta*s*L)), s=1-3tau. This order
avoids M->y->types->q->M circularity. For N>=L, choose constants soM<=3N.
Each type gets a Vandermonde linear form on F_q^B. Every good component's
distinct type IDs have exact independent uniform symbols in each block.
Thus arbitrary local heavy-state functions are integrated EXACTLY, not
via polynomial approximation, and averaging S remains valid.

Round heavy weights upward to K_b buckets, pseudo weights
w''=min(1,barw/s). Bucket symbol count floor(q*n_b/M) schedules each kept
heavy identity exactly once, leaving <K_b M/q heavy identities per pair;
all pairs share that many extra heavy-only colors because support matching.
With normalized heavy x=1/(alpha M), alpha=.75, tiny target
y=(1+delta)w/(beta*s*M), local feasibility follows beta<alpha:
load<=[H+eta_h*h+(1+delta)t]/(beta*s*M)<=1.

Unmarked tiny edges have main fractional coverage>(1+delta)w; scale each
down to exact stock. Pseudo-heavy rows with positive tiny options have
3tau slack; manuscript lem:two picks a whole color with at most2tau load
increase. Marked tiny edges use exactly ceil(Delta_mark/(1-2tau)) extra
colors by the SAME lem:two with uniform color fractions. This gives the
candidate claimed scoped count. Final independent stock audit pending.

## Other phase-6 progress

`two_matching_midpoint_single_fluid_edge_five_color_lemma.md` now treats
arbitrary p, not just midpoint: forp in[1/4,3/4], exchange mass1/5 of each
of M0,M1,empty for three recolored matchings. Scalar C_p=min(pd,(1-p)e),
G>=max(0,d+e-1), so1+G>=4C_p. Outside that p interval full+empty suffices.
Root independently checked all steps and one-fluid-edge extreme-face
reduction; audit in `one_fluid_edge_independent_audit.md`.

Naive midpoint-to-endpoint interpolation FAILS atp17/40,residuals
(A0,A1,B0,B1)=(0,17/23,1,0), deficit33/460; direct exchange repairs it.

Multiple-fluid matching extension still open. Dummy fluid matching edges
in H0 union H1 make proper3-coloring protect internal/internal fluid pairs,
but prescribed heavy-edge alignments can be infeasible due Hall cuts. Exact
examples Hpathm8,P={07,25,14,36}; m7,P={05,27,14,36}. This is a certificate
obstruction, not a hull counterexample. Root `path_chord_mixed_hull_probe.py`
checked allweights{.5,1} and7p-values for both graphs (2688instances), full
heavy-matching hull LP minimumalpha=.8. Session10761 completed. No root
process currently running.

Known exact independent-vertex activation theorem was rediscovered then
located: `bip_independent_vertex_activation_three_quarters.md`, clean leaf
induction. It is not the unresolved reciprocal-policy inequality.

Lower searches found no higher bounds. Rank-two structural exchange notes
in `rank_two_pair_atom_cycle_no_go.md`; no global theorem. General paired
independent activation alpha2/3 is FALSE, see
`general_paired_activation_two_leaf_counterexample.md`; new bridge does not
automatically apply nonbipartitely.

The global-common-arc construction from earlier phase is merely separate
heavy/tiny palettes; agent self-audited and corrected its novelty claim.
Scoped pair-forest circle smoothing remains valid, but pair-tree topology
can be reoriented bipartitely, so it is not a new general-graph extension.

## Agents

- physical-rounding agent: full new bridge and cleanup/audit.
- lower-bound agent: independent exact-stock/finite-field/final-rounding audit.
- forest agent: foundations of capped theorem/localization (passed) and
  available for extra bridge audit.

Continue working; do not promote any of these to the manuscript or declare
unrestricted improvement. Await audits, inspect scope, and preserve time
protocol. User-facing updates should remain short and avoid repeating
unchanged bounds.
