# Common-mean heavy components: capped bipartite 3/4 transfer

4 October 2026. Scoped one-color result under audit, strengthening `shared_profile_capped_heavy_transfer_audit.md`. The full weight profiles need **not** agree. This is not an unrestricted physical weighted-edge-coloring claim.

## One-color statement

Assume the combined graph is bipartite. In every connected component `P` of the heavy *endpoint-pair* support, each bundle `a=uv` has its own categorical distribution `lambda_{a,b}=x_{a,b}/x_a` on its positive heavy types, but all bundles in `P` have the same conditional **mean** weight

`mu_P=sum_b lambda_{a,b} w_{a,b}`.

Components may have different means. Let `x_a=sum_b x_{a,b}` form a bipartite fractional matching, `D_v=1−sum_{a at v}mu_P x_a`, and let tiny target `y` have incident load at most `D_v`. Give every tiny edge a cap `C_e>=12y_e`. Then one q-independent law on categorical heavy matchings with heavy marginals `3x_{a,b}/4` supports a conditional capped tiny-flow policy with coordinate means `3y_e/4`.

The theorem applies to arbitrarily large heavy components **at the one-color level**. A graph-order-uniform physical palette via the current finite-label bridge additionally needs uniformly bounded component size.

## Proof

For nonnegative tiny profits `q`, write `F_q(r,C)` for the capped bipartite flow optimum at real residual capacities `r`; write

`Phi_q(p)=E_{A_v independent Bernoulli(p_v)} F_q(1_A,C)`.

The already audited capped-flow exchange inequalities imply that the mixed derivative of `Phi_q` is nonpositive for same-shore vertices and nonnegative for opposite-shore vertices. `Phi_q` is affine in every individual coordinate.

Aggregate the heavy types in each bundle. Start at `z=(3/4)x` in the bipartite matching polytope and put `p_v(z)=1−mu_P sum_{a at v}z_a`. At the initial point `p_v=1/4+(3/4)D_v`. Alternating-path/cycle pipage rounding of `z` changes no internal vertex's aggregate degree; a cycle changes no `p`, while a path changes only its two endpoint `p` coordinates. On an odd path those endpoints are on opposite shores and their changes have the same sign; on an even path they are on the same shore and their changes have opposite signs. The signed cross derivatives therefore make `Phi_q(p(z(t)))` convex along every pipage segment. Randomly choose the segment endpoints with barycentric probabilities. This produces an integral matching `M` with `Pr(a in M)=(3/4)x_a` and

`E_M Phi_q(p(M)) >= Phi_q(p(z))`

for **every** `q>=0` simultaneously; the rounding algorithm uses only `z`, not `q`.

Conditional on `M`, draw a type `b` independently for each selected bundle `a` with law `lambda_a`, and give both endpoints of `a` the actual residual `R_u=R_v=1−w_{a,b}`. By joint concavity in vertex capacities, `F_q(R,C)>=Phi_q(R)` pointwise. For each selected edge `a=uv`, the pair `(R_u,R_v)` has equal marginals and is perfectly correlated. Conditional on the residuals at all other vertices, `Phi_q` is bilinear in this pair, with **nonnegative** coefficient of `R_uR_v` because `u,v` lie on opposite shores. Its expectation under the shared weight exceeds its expectation under two independent draws from `lambda_a` by exactly that coefficient times `Var_{lambda_a}(1−W_a)>=0`. Decouple one selected matching edge at a time. The edges are disjoint and their type draws independent, so after decoupling all covered vertex residuals are independent. Every covered vertex has mean `1−mu_P` regardless of its selected bundle. Multilinearity now gives

`E_{types|M} Phi_q(R) >= Phi_q(p(M))`.

The capped independent-activation theorem gives `Phi_q(p(z)) >= (3/4)q·y` because `C>=12y`. Consequently `E_{M,types}F_q(R,C)>=(3/4)q·y` for every nonnegative `q`. The resulting categorical matching law is independent of `q`; compact convex downward-closed support-function separation supplies **one** conditional capped-flow policy with exact tiny means `(3/4)y`.

Only the common conditional mean `mu_P` enters the pipage curvature calculation. The final type distributions can vary arbitrarily by bundle. If their means vary within `P`, the weighted residual at an internal path vertex changes under ordinary aggregate pipage, and this proof no longer applies.

## Finite-state compatibility under upward weight bucketing

Suppose every heavy component has at most `h` vertices and physical heavy weights must be rounded upward for an exact finite palette. Naively rounding each category to a common grid can destroy the exact common-mean property. It can be restored without enlarging the finite state menu beyond a function of `h` and the fixed bucket count.

Put `s=1−3tau`, where `tau` bounds each physical tiny weight. For each category, choose a first pseudo-weight `r_{a,b}>=min(1,w_{a,b}/s)` with `r_{a,b}−w_{a,b}<=eps_b` and finitely many global buckets (for instance `r=min(1,barw/s)` after upward grid rounding `barw`, with `eps_b<=(eta_h+3tau)/(1−3tau)`). This stronger lower bound is needed for the later additive `2tau` tiny-edge row rounding: if a selected pseudo-weight is below one, then `w+s(1−r)<=s`, leaving `3tau` row slack; if it is one, no tiny flow touches that endpoint. Let `m_a=sum_b lambda_{a,b}r_{a,b}` and `c_P=max_{a in P}m_a`. Define

`t_a=(c_P−m_a)/(1−m_a)` if `m_a<1`, and `t_a=0` if `m_a=1`; then set `w''_{a,b}=r_{a,b}+t_a(1−r_{a,b})`.

We have `w''_{a,b} in [r_{a,b},1]` and `sum_b lambda_{a,b}w''_{a,b}=c_P` for every bundle. Since the original bundle means all equal `mu_P`, `0<=c_P−mu_P<=eps_b`. The padding may move an individual rare low-weight type far upward when `c_P` is near one, but the mean increase per bundle is at most `eps_b`. There are still at most `(h choose 2)` bundles and a fixed number of original buckets per component, so the number of categorical pseudo-states stays bounded in `h,eps_b`.

If sampled/pruned tiny load is at most `D_v+eta_s`, scale **both** the heavy target and sampled tiny target by `kappa=1/(1+eta_s+eps_b)`. At every vertex, aggregate heavy degree is at most one, so

`kappa [sum_{a at v}c_P x_a + (D_v+eta_s)] <= kappa[1+eps_b+eta_s]=1`.

Thus the common-mean one-color input applies to the pseudo-weights and scaled targets. The discarded heavy fraction and tiny target are `O(eta_s+eps_b)`, absorbable in a `(4/3+epsilon)` physical palette. Exact heavy identity bookkeeping, local forest flow policies, and color-block construction still require the separate audited bridge; this paragraph establishes only that upward bucketing does not invalidate the one-color hypothesis.

## Checks and limits

The real-capacity signed cross inequalities used in the narrower shared-profile proof were stress-tested on 2,500 random capped 3-by-3 bipartite instances, with maximum violation below `9e−16`. The **common-mean proof above does not need them**: it uses only the binary-activation shore signs for `Phi_q` and the simple bilinear covariance identity. No numerical test substitutes for the exchange proof.

The result remains scoped to bipartite combined support, common conditional mean inside each heavy component, and divisible one-color tiny flows. The current physical bridge additionally needs bounded heavy-component size and its full parameter/stock audit. Arbitrary means within a component, unbounded component state menus in the physical palette, and nonbipartite recourse remain open here.

Cutting a large heavy component into bounded pieces by discarding only an arbitrarily small amount of heavy fractional stock is not a general remedy. On a fixed-degree bipartite expander with `x_e=1/d`, every partition into components of size at most a fixed `B<n/2` cuts a positive fraction of all edges by expansion, hence a positive fraction of total `x` mass. A uniform physical extension therefore needs a genuinely local heavy matching law or a palette mechanism that can reproduce long-range heavy correlations; simple heavy-support component cutting cannot give vanishing loss.
