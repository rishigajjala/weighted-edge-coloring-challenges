# A scoped physical palette for matching-heavy support and fluid degree two

4 October 2026. Research candidate under audit. This note does **not** assert an unrestricted weighted-edge-coloring bound. It isolates a physical integer transfer when heavy simple support is a matching and the underlying simple tiny support has maximum degree two (arbitrary tiny parallel multiplicity). The one-color coefficient is `alpha=2/3`, so the leading palette coefficient is `3/2`, not the broader bipartite `4/3` target.

## Explicit hypotheses and target

Let every physical edge have weight in `(0,1]`. Declare heavy edges to have weight **strictly greater than** `1/2`; their underlying simple support is a matching of vertex pairs `P_i`. Every other edge is tiny, of weight at most `tau`. At a vertex, at most two **distinct endpoint pairs** support tiny edges; there may be arbitrarily many physical parallel tiny identities on either pair. Let `N` satisfy both the physical weighted degree bound `sum_{e at v}w_e<=N` and the heavy count bound `n_i<=N` for each heavy pair. For `P_i`, put `n_i=sum_b n_{i,b}`, `x_i=n_i/N`, and `mu_i=(sum_b n_{i,b}w_{i,b})/n_i` when `n_i>0`. For each physical tiny edge `e`, put `y_e=w_e/N`; local feasibility is `sum_{tiny e at v}y_e<=D_v:=1−mu_i x_i` on a vertex of pair `i`, and `D_v=1` at a heavy-free vertex.

The heavy count bound is automatic with `N=bp(G)` under the strict `>1/2` cutoff: a unit bin contains at most one incident heavy edge. The proof itself only needs the two stated bounds, so it also applies at weight exactly `1/2` if `n_i<=N` is imposed separately. An algorithm need not compute local bin-packing numbers: take `N=max{ceil(Delta_w(G)), max_i n_i}`, which is at most `bp(G)` under the strict cutoff.

The candidate consequence is: for every `epsilon>0`, choose a sufficiently small `tau(epsilon)>0`; then, for all sufficiently large `N`, a proper weighted coloring uses at most `(3/2+epsilon)N+O_epsilon(1)` colors, uniformly in graph order, parallel multiplicity, and smallest positive tiny weight. All heavy and tiny **physical identities** are colored exactly once. This is conditional only on the source-preserving two-row option lemma already stated as `lem:two` in `output/pdf/weighted_edge_coloring_1999_current.tex`; the one-color inequality and palette steps are proved below for audit.

## One-color capped formula

First, for arbitrary categorical heavy profiles on the disjoint pairs, let `alpha=2/3`. Select pair `i` iff one common uniform `U` lies below `alpha x_i`. Conditional on selection, draw its heavy type from the pair's categorical profile, independently across pairs. Its residual `R_i` is `1−W_i` when selected and one otherwise; both vertices of the pair share this residual. A heavy-free vertex has residual one. Set `a_i=mu_i x_i=1−D_i`. For distinct pairs,

`m_ij=E R_iR_j=1−alpha(a_i+a_j)+alpha min(a_i mu_j,a_j mu_i)`.

The elementary inequality `mu_i>=a_i` follows simply from `x_i<=1`, even if the categorical weights are below `1/2`. Thus `min(a_i mu_j,a_j mu_i)>=a_i a_j`, giving the stronger, uniform bound

`m_ij >= [1+2D_iD_j]/3`.

For an edge internal to one heavy pair, `m_ii=E R_i²=1−2alpha a_i+alpha x_i E W_i²`. Jensen gives `x_i E W_i²>=x_i mu_i²=a_i mu_i>=a_i²`, so `m_ii>=[1+2D_i²]/3`. Heavy-free vertices can be represented by `x=0,D=1`. In all cases `m_ij>=1/3`. The weight-`1/2` cutoff is therefore irrelevant to this one-color product inequality; the physical coloring formulation retains its declared heavy/tiny split.

For each physical tiny edge `e=uv`, define one-color divisible allocation

`f_e(R)=alpha y_e R_uR_v/m_uv`.

It has exact mean `alpha y_e` and pointwise cap `f_e<=2y_e`. Parallel identities have the same product/denominator, and summing them simply replaces their individual `y_e` by bundle total `Y_uv`. At a vertex with `D_v=d`, every incident bundle target `Y` satisfies `Y<=D_neighbor` and the bundle totals sum to at most `d`. Therefore, if `R_v>0`,

`sum_{e at v} f_e/R_v <= sum_{bundles uv at v} g_d(Y_uv)`, where `g_d(Y)=2Y/(1+2dY)`.

This uses `D_neighbor>=Y` and monotonicity of the product lower bound in `D_neighbor`. The function `g_d` is concave on all nonnegative `Y`. There are at most two simple tiny neighbors, hence Jensen and `sum Y<=d` give

`sum g_d(Y)<=2g_d(d/2)=2d/(1+d²)<=1`.

Thus every state has `sum_{e at v}f_e<=R_v`. If `R_v=0`, every incident allocation is zero. The argument uses the degree-two condition only after aggregating physical parallels.

## Fixed finite-field block and exact ideal law

Choose a fixed heavy bucket width `eta_h>0`, a prime-power `q` large compared with the number `K` of buckets, and `q>=5`. Put `L=q²`, `s=1−3tau`, and choose a fixed small `rho>0` satisfying

`rho>=2(eta_h+sK/q)`.

Take `B=ceil((1+rho)N/(s alpha L))` blocks and `M=BL` main colors. Thus `M>=(1+rho)N/(s alpha)` and `M<=(1+rho)N/(s alpha)+L`. For a heavy identity with actual weight `w`, round to a finite upper bucket `barw in[w,w+eta_h]` and define its **ideal** pseudo-weight `r=min(1,barw/s)`. If `r<1`, then `w<=s r`; if `r=1`, an ideal selected heavy pair has zero tiny residual at both endpoints. Also `r<=(w+eta_h)/s`.

For each heavy pair, let `k_i=floor(n_i/L)` (and `k_i=0` if `n_i=0`). In every one of its first `k_i` blocks the pair is ideally occupied, and in later blocks it is ideally empty. Because all pairs use the same block order, these ideal occupancy events are **nested**. Its ideal occupancy probability is `p_i=k_i/B=alpha x_i^0`, where `x_i^0=k_i/(alpha B)<=s x_i/(1+rho)<=1`.

Within a selected block, bucket `b` has physical count `n_{i,b}`. Assign exactly `m_{i,b}=floor(q n_{i,b}/n_i)` of the `q` field symbols to bucket `b`. Assign the fewer than `K` remaining symbols to a **ghost ideal category** of pseudo-weight one. A ghost means the ideal residual is zero, but no physical heavy identity is placed in that color. Every actual scheduled heavy identity has actual weight at most its ideal pseudo-weight; hence actual residual is always at least ideal residual. Conditional on ideal occupancy, the ideal mean pseudo-weight `mu_i^0` obeys

`mu_i^0 <= (mu_i+eta_h)/s + K/q`.

Consequently `x_i^0 mu_i^0 <= x_i(mu_i+eta_h+sK/q)/(1+rho) <=x_i mu_i`, where the last inequality uses `mu_i>=1/2` and the choice of `rho`. The ideal local residual target `D_i^0=1−x_i^0 mu_i^0` is therefore at least the original `D_i`. Every original tiny `y_e` remains feasible for the one-color formula under the ideal law.

Contract each heavy pair. A contracted pair touches at most four other pairs through tiny edges, since each of its two physical vertices has at most two simple tiny neighbors. Properly color this interaction graph with five labels. Choose five distinct slopes `t_1,...,t_5` in `F_q`. In every block enumerate all `(a,b) in F_q²`; in the color indexed by `(a,b)`, a pair carrying label `j` uses symbol `a+t_j b`. Each symbol is uniform over a block, and symbols of any two **adjacent** pairs are exactly independent because the two-slope linear map is invertible. The field enumeration is repeated identically in every block. Internal tiny edges use the one pair's symbol and residual squared. Thus the empirical average over all `M` colors is exactly the common-prefix occupancy law with independent conditional types for every fluid-adjacent pair; no graph-order-dependent concentration or minimum tiny weight enters.

## Exact heavy stocks and tiny option rounding

In each occupied block, each field symbol occurs exactly `q` times at each pair. Hence bucket `b` receives `k_i L m_{i,b}/q` main heavy slots, an integer no larger than `n_{i,b}` because `m_{i,b}/q<=n_{i,b}/n_i` and `k_iL<=n_i`. Assign a distinct physical identity from that bucket to every nonghost slot. The heavy leftovers at pair `i` total

`n_i−k_iL sum_b(m_{i,b}/q) < L+K M/q`.

Since distinct heavy pairs are vertex-disjoint, all heavy leftovers can be placed in fewer than `L+K M/q+1` additional heavy-only colors, one leftover identity per pair per color.

Let `R_v(c)` be the ideal residual at vertex `v` in main color `c`, and define the **empirical** denominator

`m_e=(1/M)sum_{c=1}^M R_u(c)R_v(c)`.

The finite-field construction makes `m_e` equal to the preceding ideal-law product expectation; in particular `m_e>=1/3`. Give each physical tiny edge `e=uv` the probability distribution over main colors

`pi_{e,c}=R_u(c)R_v(c)/(M m_e)`.

This is nonnegative and sums to one **for each physical identity**, regardless of how small `w_e` is. By the one-color formula, the expected tiny weight in any vertex/color row is

`sum_{e at v} w_e pi_{e,c} = (N/(M alpha)) sum_{e at v} f_e(R(c)) <= (N/(M alpha)) R_v(c) <= s R_v(c)/(1+rho)`.

Apply the manuscript's one-option-per-job lemma (`lem:two`) with each job a physical tiny edge, each option a main color, and the two affected rows its endpoint/color constraints. Every option consumes at most `w_e<=tau`, so a deterministic selection uses at most the displayed fractional row load plus `2tau` in every row. If an actual heavy identity occupies a row and its ideal pseudo-weight `r<1`, then `w_actual<=sr` and the final load is at most `sr+s(1−r)+2tau=s+2tau=1−tau<1`. If `r=1`, ideal residual and all tiny option probabilities at that endpoint are zero, so the row contains only the heavy identity of weight at most one. Ghost rows contain no actual heavy identity and are safer. Thus every main color is feasible, and every tiny physical identity receives exactly one color.

The total color count is at most

`M + L + K M/q + 1 <= [(1+rho)(1+K/q)/(s alpha)]N + O(q²)`.

Choosing `tau,eta_h,rho,K/q` small in that order gives `(3/2+epsilon)N+O_epsilon(1)`. The constants depend on `epsilon` but not graph order, parallel multiplicity, or the smallest positive weight.

## Exact remaining limits

This construction relies on an underlying **matching** of heavy pairs to schedule all leftover heavy identities in the same extra colors, and on simple tiny degree at most two for the pointwise `g_d` row inequality. The adjacent-pair field trick uses only pairwise independence; it does not supply the capped `3/4` policy needed for a `4/3` palette. The root agent independently checked the ghost-slot, field-moment, stock, parameter, and manuscript `lem:two` interfaces on 4 October; the present scratch proof has not been integrated into the manuscript or Lean files. For fixed `epsilon`, the field and bucket sizes are constants and `M=O(N)<=O(m)`. With rational input weights and rational fixed parameters, deterministic option rounding uses finite rational arithmetic.
