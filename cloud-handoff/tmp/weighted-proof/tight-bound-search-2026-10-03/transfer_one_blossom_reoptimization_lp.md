# Exact conditional LP for reoptimizing fluid inside one tight blossom

**Status: proved conditional reduction; unrestricted repair inequality open.** This follows the audited disjoint-maximal-tight-blossom projection in `transfer_disjoint_tight_blossom_projection.md`. It allows baseline unit fluid edges to move along arbitrary alternating paths. It does **not** assert that the repair LP is always feasible.

Fix a locally feasible `(x,y)`, `alpha=2/3`, a coordinatewise maximal matching-polytope projection `z'<=z=(alpha x,alpha y)` retaining all heavy coordinates, and one distribution `mu` on ordinary unit matchings with mean `z'`. Let `S` be one maximal tight odd set, so every matching state contains exactly `(|S|-1)/2` internal unit edges. All reduced fluid types have both endpoints in a unique such maximal set. Write `F(S)` for fluid types internal to `S`.

For a unit matching state `M`, **retain** every selected heavy type as a physical heavy item and every selected fluid type *outside* `F(S)` as a full unit of physical fluid. **Release** the selected unit fluid types in `F(S)`; these can be replaced by any internal fluid flow. Let `r^S_v(M)` be the residual physical capacity at `v in S` after the retained items:

* `r^S_v=1-w_e` if `v` is covered by a selected heavy edge `e` (internal or crossing);
* `r^S_v=0` if `v` is covered by a retained crossing unit fluid edge;
* `r^S_v=1` otherwise.

These cases are exclusive because `M` is an ordinary matching. In particular, an internal unit fluid edge from `M` no longer occupies its endpoints in this residual calculation. For each state introduce nonnegative **state-weighted** replacement amounts `u_{M,f}` for `f in F(S)`. The exact fixed-`mu` repair LP is

`sum_M u_{M,f}=alpha y_f` for every `f in F(S)`,

`sum_{f in F(S):v in f}u_{M,f} <= mu_M r^S_v(M)` for every `M` and `v in S`,

`u>=0`.

If this LP is feasible for every maximal tight blossom `S`, processing the blossoms simultaneously yields an actual global weighted pattern distribution with means `(alpha x,alpha y)`: the blossom vertex sets are disjoint, all outside unit fluid edges retain their original means, and internal fluid means are restored exactly. Conditional sampling is unnecessary here because each state can be assigned a deterministic fractional flow `u_{M,f}/mu_M` when `mu_M>0`. Conversely, for the **fixed** heavy law and fixed outside unit-fluid edges encoded by `mu`, any restoration confined to internal fluid types satisfies this LP, so the LP is exact for that conditional subproblem. One may still improve feasibility by choosing a different decomposition `mu` or by changing the outside pattern; fixed-`mu` failure would not refute the global `3/2` theorem.

The baseline unit-matching internal fluid vector `u^0_{M,f}=mu_M 1_{f in M}` is feasible and has means `z'_f`. The new LP permits decreasing this baseline on some states and increasing it on others: it captures alternating-path replacements, unlike an append-only residual-capacity check.

The **total** fluid removed inside each maximal tight blossom is strictly less than `1/2`, irrespective of its size or nested tight subsets. Write `S` as `2k+1` vertices, `d_S=sum_{f in F(S)}(z_f-z'_f)`, `R_S=sum_{v in S}sum_{e heavy incident v}(1-w_e)x_e`, and `c_S` for the *unscaled* total heavy-plus-fluid mass on edges crossing `S`. All reduced fluid types internal to `S` contribute to `z(E(S))-z'(E(S))`; since `S` is tight, `d_S=z(E(S))-k`. Summing the local weighted-capacity inequalities over `S` gives

`z(E(S)) <= (|S|+R_S-c_S)/3`.

Every vertex has heavy count at most one and every heavy weight exceeds `1/2`, so `R_S<|S|/2=k+1/2` whenever there is heavy mass; if there is none, `R_S=0` and the same strict upper bound holds. Therefore

`0<=d_S<1/2-c_S/3<=1/2`.

This is only a scalar *amount* bound. It does not settle whether the removed fluid can be placed on its prescribed internal edge types under a common matching law; that requires the full inequality (★) below.

For a **single chosen profit vector** `q>=0`, one may instead choose `z'` to maximize `q·z'_F` among ordinary-matching points with fixed heavy coordinates and `z'_F<=z_F`. At that optimum all degree rows remain strict, so a dual optimum can be chosen with zero degree prices and nonnegative prices `lambda_T` only on tight odd-set rows (besides fluid upper/lower bounds and unrestricted heavy-equality prices). For a reduced fluid type `f`, its upper-bound multiplier is zero. LP stationarity then gives

`q_f=sum_{T tight odd: f in E(T)} lambda_T` if `z'_f>0`,

`q_f<=sum_{T tight odd: f in E(T)} lambda_T` if `z'_f=0`.

Thus the profit of any removed edge is paid by tight-blossom shadow prices. This is a precise alternating-path proof route: show that physical residual capacity earns enough of each shadow price while preserving the heavy law. The dual statement alone does not furnish such a packing or imply (★).

A direct exchange version is also exact. Fix such a `q`-optimal projection and any decomposition `mu`. Let `f=uv` be a reduced internal fluid edge, and suppose a positive-probability matching state `M` is globally free at `u` (including no crossing edge) and internally matches `v` by a fluid edge `g=vt`. Then `M-g+f` is another ordinary matching with precisely the same heavy set. Transferring a small amount of probability from `M` to this new state leaves every heavy mean fixed, decreases the `g` fluid mean, and increases the `f` mean; all fluid upper bounds remain satisfied for a sufficiently small transfer because `f` is reduced. Optimality therefore forces `q_f<=q_g`. If instead `g` is heavy, retaining it physically leaves `1-w_g>=0` capacity at `v`; this permits a positive insertion of `f` only when `w_g<1`. Thus a reduced fluid type can face only a no-loss-or-uphill fluid exchange or a heavy edge with possibly zero residual at every globally free exposure of either endpoint. This is a qualitative statement; it supplies no simultaneous quantitative routing bound for all reduced types.

This exchange can be made **acyclic** by selecting, among `q`-optimal projections, one that lexicographically maximizes fluid coordinates in an order of nonincreasing `q_f`. If a reduced `f` is ranked before `g`, the same perturbation is impossible even when `q_f=q_g`, because it improves the first changed lexicographic coordinate. Hence every fluid `g` matched opposite a globally free endpoint of reduced `f` must rank **strictly earlier** than `f`. In particular, **if the first-ranked fluid type overall is reduced**, all such opposite matches are heavy; the resulting direct physical insertion capacity is `1-w_g` and may be zero when `w_g=1`. An earlier fluid type at its upper bound may obstruct a later reduced type; the acyclic hierarchy does not prove that the available capacity pays all deficits simultaneously.

There is a useful decomposition-independent exposure identity. Write `S` as `2k+1` vertices and let `c_v` be the mean selected unit edge crossing `S` at vertex `v`. Since every `M` has exactly `k` internal edges, a vertex `v` is exposed by the internal matching with probability `1-deg_{E(S)}z'(v)`. It is exposed **and globally unmatched** with probability

`1-deg_{E(S)}z'(v)-c_v =1-deg z'(v)>0`.

The strict positivity follows from the original scaled local degree bound. The total free-exposure probability is `sum_{v in S}(1-deg z'(v))=1-z'(delta(S))`; at most one crossing unit edge can be selected in a state with `k` internal edges. These identities hold for every decomposition `mu`, but they do not force a free exposed vertex to coincide with a useful selected heavy edge. Such joint compatibility is the unresolved alternating-path issue.

They also give a useful **support-level factor-criticality** statement. Let `G^+_S` contain precisely the internal heavy and fluid types with `z'_e>0`, viewed as unweighted edges. For each `v in S`, the positive free-exposure probability above supplies at least one matching state whose `k` internal selected edges lie in `G^+_S` and cover `S\{v}`. Hence `G^+_S-v` has a perfect matching for every `v`: the positive-support graph of **every** tight odd set is factor-critical. In particular it is connected when `|S|>=3`. This guarantees ordinary alternating-path access through the unit support, but it does not by itself preserve selected heavy edges or pay for the prescribed fluid replacements.

For a nonnegative internal fluid profit vector `q`, define

`F^S_q(r)=max{sum_{f in F(S)}q_f t_f:t>=0, sum_{f in F(S):v in f}t_f<=r_v for every v in S}`.

The set of achievable mean internal fluid vectors for fixed `mu` is compact, convex, and coordinatewise downclosed. Therefore the repair LP is feasible **if and only if**, for every `q>=0`,

`sum_{f in F(S)}q_f alpha y_f <= sum_M mu_M F^S_q(r^S(M))`.       (★)

This follows by support-function separation; nonnegative `q` suffice because both the achievable set and the target nonnegative orthant are downclosed. Writing `d_f=alpha y_f-z'_f>=0`, the same condition is the exact incremental-gain inequality

`sum_M mu_M F^S_q(r^S(M)) - sum_{f in F(S)}q_f z'_f >= sum_{f in F(S)}q_f d_f`.

The left side is the maximum profit gain from **reoptimizing all internal fluid** in each weighted heavy state, relative to the released unit-fluid baseline. It can be strictly larger than the gain available by merely appending fluid to baseline matchings. Proving (★) for a suitable matching decomposition `mu`, simultaneously for all disjoint maximal tight blossoms, is a concrete sufficient route to the full unrestricted heavy-plus-fluid `3/2` inclusion. No universal proof or exact counterexample to (★) is known here.

There is an exact minimax form that permits the decomposition itself to depend on a separating profit vector. Let `D(z')` be the compact polytope of all laws on ordinary matchings with mean `z'`. For each state `M`, release unit fluid inside **every** maximal tight blossom simultaneously, retain all other selected items, and let `r^S(M)` be the capacity vector above. The union of attainable mean internal-fluid vectors over `mu in D(z')` is itself compact, convex, and downclosed: mixtures of two laws and their state-weighted flow allocations preserve the same mean `z'`. Thus a common law and conditional replacement flows exist for all blossoms if and only if, for every collection of nonnegative internal-fluid prices `q=(q^S)_S`,

`max_{mu in D(z')} sum_M mu_M sum_S F^S_{q^S}(r^S(M)) >= alpha sum_S q^S·y_{F(S)}`.       (★★)

The same `mu` appears in all blossoms **inside** the maximization. Testing each blossom with a separately optimized law would be weaker and does not imply simultaneous repair. For fixed `q`, the left side of (★★) is a finite LP. Its dual is

`min {theta_0+sum_e theta_e z'_e : theta_0+sum_{e in M}theta_e >= sum_S F^S_{q^S}(r^S(M)) for every ordinary matching M}`,

with unrestricted `theta_0,theta_e`. This is the exact linear majorant certificate for a failure of the chosen projection. Proving (★★), or finding a violating `q` and its dual certificate for every admissible projection, is the remaining general problem.

For comparison, if **all** unit fluid is released globally and only the projected heavy law `nu` is retained, there is a compact dual covariance identity. Let `r_v(A)=1-sum_{e in A:e incident v}w_e`, let `F_q(r)` be the global fractional fluid packing value, and choose for each heavy matching `A` an optimal dual vertex cover `b^A>=0` with `b^A_u+b^A_v>=q_f` on every fluid type. Put `L_v=sum_{e heavy incident v}w_e x_e`; local feasibility gives `deg_v y<=1-L_v`. If `Pr_nu(e in A)=alpha x_e`, then

`E_nu F_q(r(A)) - alpha q·y >= (1/3) E_nu sum_v b^A_v - sum_e w_e Cov_nu(1_{e in A}, b^A_u+b^A_v)`.

Indeed `F_q(r(A))=sum_v r_v(A)b^A_v` by LP duality, while `q·y<=sum_v(1-L_v)b^A_v` in each state; subtract and collect means. A suitably balanced matching law could control the covariance term, but no universal such bound is proved. The identity is not a substitute for the exact state-dependent recourse LP: some heavy laws have adverse covariance even when another law succeeds.

The omitted local and dual slacks are nonnegative and may be needed at equality. With `sigma_v=1-L_v-deg_v y>=0` and `s_f^A=b^A_u+b^A_v-q_f>=0`, the **exact** identity is

`E_nu F_q(r(A)) - alpha q·y = (1/3) E_nu sum_v b^A_v + alpha sum_v sigma_v E_nu b^A_v + alpha sum_f y_f E_nu s_f^A - sum_e w_e Cov_nu(1_{e in A}, b^A_u+b^A_v)`.

Consequently the bare covariance bound is sufficient but may be unnecessarily strong; a correct charging proof can also use the two explicit slack terms.

For the **uniform fluid-profit direction** `q_f=1`, the statewise recourse has a second exact form. On the fluid support graph, let `I` range over independent vertex sets and set `Delta_r(I)=r(I)-r(N(I))`. Fractional vertex-cover half-integrality gives

`F_1(r)=1/2 [sum_v r_v - max_{I independent} Delta_r(I)]`.

To see this, an optimal dual cover may be chosen with values in `{0,1/2,1}`. Its zero set `I` is independent; vertices in `N(I)` have value one, and all remaining vertices may be assigned `1/2`. Minimizing the resulting cost over `I` yields the formula. Hence uniform-profit repair is equivalent to controlling the **expected maximum independent-set residual imbalance** under the heavy matching law. This is an arbitrary-size exact reduction, not a proof of the bound; the maximum and expectation cannot simply be interchanged, and general fluid profits need the full vertex-cover dual.
