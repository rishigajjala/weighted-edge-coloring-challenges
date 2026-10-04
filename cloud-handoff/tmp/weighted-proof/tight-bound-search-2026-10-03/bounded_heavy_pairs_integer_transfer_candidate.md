# Finite-palette transfer with a bounded number of heavy pairs

**Status (2026-10-03): candidate restricted theorem for independent audit.** This is scratch research during the user-requested five-hour exploration period. It does not settle graphs with an unbounded number of heavy-support pairs or the unrestricted weighted edge-coloring bound.

## Candidate statement

Fix an integer `H>=0` and any accuracy `epsilon>0`. Let `G` be a finite loopless weighted multigraph whose combined support is bipartite. Every edge is either heavy, of weight greater than `1/2`, or tiny, of weight at most `tau`; the simple heavy support is a matching of at most `H` pairs. If every physical vertex list packs into `N` unit bins, then for sufficiently large `N` (depending only on `H,epsilon`) and sufficiently small `tau` (depending only on `epsilon`), the physical edges admit an integer coloring with at most `(4/3+epsilon)N+1` colors. The threshold is independent of the number of vertices, tiny-edge multiplicity, and smallest positive tiny weight.

The proof below is conditional only on the capped one-color theorem and capped opposite-side exchange in `physical_tiny_cap_rounding_route.md`, both separately audited in `five_hour_capped_activation_audit.md`. It uses a finite number of heavy pairs in one step: uniform approximation of their joint categorical color-state law.

## Parameters and heavy weight buckets

Put `alpha=3/4`. Choose positive constants `eta,delta,rho` so small that `eta+delta<=rho` and `4(1+rho)/[3(1-3tau)]<=4/3+epsilon` for the admitted `tau`. Put `s=1-3tau>0` and

`M=ceil((1+rho)N/(alpha s))`.

Round each heavy physical weight upward to a bucket representative `bar w_h<=min(1,w_h+eta)`. There are at most `K=ceil(1/(2eta))+1` possible heavy bucket labels in `(1/2,1]`, a constant depending only on `eta`. At each heavy pair `P`, let `n_(P,b)` be its number of heavy physical edges in bucket `b`; `sum_b n_(P,b)<=N` because local bins hold at most one heavy edge. Define the pseudo-heavy weight `w''_b=min(1,bar w_b/s)`.

For a prospective one-color distribution, give every heavy physical edge pseudo-marginal `x'_h=1/(alpha M)`, and every tiny edge normalized load target

`y'_e=(1+delta)w_e/(alpha s M)`.

At a vertex `v`, let `H_v` be total actual heavy weight, `h_v` heavy count, and `t_v` tiny weight. Local feasibility gives `H_v+t_v<=N` and `h_v<=N`. Since `s w''_b<=bar w_b<=w_h+eta`, its pseudo-heavy plus normalized tiny target load is at most

`[H_v+eta h_v+(1+delta)t_v]/(alpha s M) <= [N+(eta+delta)N]/[(1+rho)N] <=1`.

The capped heavy matching theorem therefore applies to the pseudo-heavy categorical states with normalized per-edge cap `C'_e=12y'_e`. After scaling every tiny flow by `s`, the one-color law has actual heavy probability `1/M` per physical identity and tiny mean `(1+delta)w_e/M`. Its actual per-color tiny cap is

`C^act_e=s C'_e=12(1+delta)w_e/(alpha M) <=w_e`

for all sufficiently large `N`. The actual tiny load at a vertex in a bucket-heavy state is at most `s(1-w''_b)=(s-bar w_b)_+`; in an empty state it is at most `s`. Thus every positive tiny load has at least `3tau` slack below the actual residual after the physical heavy identity is later assigned to that bucket slot.

## An exact bucket schedule close to the product law

For each pair `P`, its categorical one-color bucket law has probability `n_(P,b)/M` for bucket `b` and the remaining probability for empty. The `H` pairs are independent in the one-color theorem. Let `pi` be their product law on at most `(K+1)^H` joint bucket states.

There is a deterministic list of `M` joint states whose empirical law `hat pi` has total-variation distance `o_(H,K)(1)` from `pi` and whose marginal bucket counts at each pair are **exactly** `n_(P,b)`. To see this, sample `M` joint states independently from `pi`. The expected total absolute deviation of all joint-state counts is `O(sqrt(M (K+1)^H))`; the expected sum of all pair/bucket marginal count deviations is `O(H sqrt(M(K+1)))`. Choose a realization within the sum of these bounds up to a constant. For each pair independently, edit the bucket label in at most half the `L1` marginal discrepancy many color slots to correct its counts, including empty labels. Every edit changes at most one joint-state count down and one up. Consequently

`TV(hat pi,pi)=O_(H,K)(M^(-1/2))`.

Now assign each actual heavy physical edge of bucket `b` to one of that pair's `n_(P,b)` bucket slots bijectively. This uses each heavy edge exactly once, never uses two from one heavy pair in one color, and each chosen actual weight is at most its slot's bucket upper weight. The tiny recourse polytope in a color depends only on the joint bucket state, so the empirical support sum is independent of the individual identity assignment.

## Uniform support comparison and exact tiny stocks

Fix any `q>=0`. Let `F_q(a)` be the maximum **actual scaled** tiny profit in one color with joint bucket state `a`, vertex capacities `s(1-w''_b)` (or `s` when empty), and edge caps `C^act_e`. The capped one-color theorem gives

`E_(a~pi) F_q(a) >= (1+delta) q·w/M`,

where `w=(w_e:e tiny)`. Pointwise,

`0<=F_q(a)<=sum_e q_e C^act_e=[12(1+delta)/(alpha M)] q·w`.

Therefore the chosen empirical schedule satisfies, **simultaneously for every nonnegative `q`**,

`sum_(c=1)^M F_q(a_c) = M E_(hat pi)F_q(a) >= [1+delta-24(1+delta)TV(hat pi,pi)/alpha] q·w`.

For `N` sufficiently large in terms of `H,eta,delta`, the bracket is at least one. By support-function separation and downward closure of the Minkowski sum of the `M` capped-flow polytopes, there are actual tiny loads `z_(e,c)` satisfying `0<=z_(e,c)<=C^act_e<=w_e`, `sum_c z_(e,c)=w_e` for every physical tiny edge, and all state-dependent per-color vertex capacities. Thus the finite table has exact physical tiny stocks before rounding.

## Rounding the tiny color choices

Set `x_(e,c)=z_(e,c)/w_e` for every positive-weight tiny edge. Each source row has `sum_c x_(e,c)=1`. Each vertex/color weighted load is at least `3tau` below the capacity left by its actual assigned heavy edge wherever a tiny variable is positive. Apply the bipartite source-preserving iterative rounding lemma in `physical_tiny_cap_rounding_route.md`: maintain source equations and each vertex/color load row while it has at least four fractional variables. The rank count, plus a left-minus-right row dependency in the equality case, supplies a nullspace move until every variable is zero or one. Every released vertex/color row can rise by at most `3tau`. The resulting integer choice assigns every physical tiny edge exactly once, and every color is feasible alongside its already assigned physical heavy edges.

This proves the candidate bound for fixed `H`, subject to checking the one-color capped theorem and the row-dependency rounding argument in full. The bottleneck for unbounded `H` is visible: `(K+1)^H` joint heavy bucket states cannot be approximated in total variation by only `M=Theta(N)` empirical colors. The uniform `q` comparison fails without a different metric or a local concentration argument.
