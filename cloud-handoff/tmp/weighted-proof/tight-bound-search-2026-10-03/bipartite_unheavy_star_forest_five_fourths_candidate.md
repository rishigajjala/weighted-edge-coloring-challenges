# Candidate 4/5 transfer for bipartite heavy plus unheavy-centered fluid star forests

**Interim status (2026-10-03, before the user's five-hour research deadline):** complete candidate proof under the stated star-forest and heavy-free-center hypotheses. It extends the earlier 3/4 star-forest phase result. This is an uncapped, divisible-fluid local-hull statement, not an integer physical-edge-coloring theorem or a result for arbitrary fluid forests.

Let the combined graph be bipartite. Heavy physical types have arbitrary weights `w_h∈[1/2,1]`, and one-color heavy sets are matchings. Fluid edges form a vertex-disjoint star forest; **no heavy edge is incident to any star center**. Heavy simple support may otherwise be arbitrary, with parallel heterogeneous types. Let the local point satisfy `Σ_{h∋v}x_h<=1` and `Σ_{h∋v}w_hx_h+Σ_{e∋v}y_e<=1`. The candidate conclusion is that `((4/5)x,(4/5)y)` lies in the one-color mixed hull.

Fix nonnegative fluid profits `q` and order each star's leaves in nonincreasing profit order. Let `p_i=Σ_{h∋v_i}x_h` be heavy occupancy probability of leaf `i`, and `L_i=Σ_{h∋v_i}w_hx_h` its mean heavy load. Put `D_i=1−L_i`. Each center has capacity exactly one.

Parallel fluid edges between one center and one leaf cause no change: for the fixed support direction `q`, replace that parallel family by one virtual spoke of profit equal to its largest `q_e`. The recourse optimum uses that best spoke, while the target profit is at most the virtual profit times the total target fluid on the leaf pair. Apply the proof to distinct leaf **vertices**, with each virtual spoke's target equal to the sum of parallel target loads. This preserves the support inequality for every physical fluid-profit vector.

## A full heavy law balancing the first two and three leaves

For every star `S` and `k=2,3` up to its leaf count, put `P_{S,k}=Σ_{i<=k}p_i`. Require every sampled full heavy matching `M` to have

`floor(P_{S,k}) <= # {top-k leaves covered by M} <= ceil(P_{S,k})`.  (1)

These requirements can be imposed **simultaneously** while preserving every physical heavy marginal `x_h`. On either bipartition shore, the top-two set lies inside the top-three set for each star, while sets from distinct stars are disjoint. They form a laminar quota family. Construct a flow network from a source through the laminar group trees and individual vertices of the left shore, then across arcs representing physical heavy types, then through right-shore vertices and their laminar group trees to a sink. Give each vertex capacity one, each `top-k` group arc lower capacity `floor(P_{S,k})` and upper capacity `ceil(P_{S,k})`, and all other arcs their natural bounds. The fractional heavy vector `x` induces a feasible network flow. Integral lower/upper arc bounds and network total unimodularity decompose it into integral flows; their selected heavy arcs are matchings satisfying (1), and their average is exactly `x`. This argument also covers parallel heavy types as parallel arcs.

## Five globally synchronized deletion phases

Condition on any full heavy matching `M` from this law. Construct an auxiliary bipartite multigraph whose vertices are the fluid stars, placed on the shore of their leaves. A selected heavy edge touching a top-four leaf of two stars becomes an auxiliary edge between the stars. If it touches top-four leaves at only one star, attach a private degree-one dummy auxiliary endpoint on the opposite shore. Selected heavy edges touching no top-four leaf are ignored for this graph. Every star has auxiliary degree at most four. Because the original combined graph is bipartite, so is the auxiliary graph. Properly edge-color it with phase colors `1,2,3,4`. Assign phase `5` to every selected heavy edge ignored above. Choose `T` uniformly from `{1,...,5}` and delete every selected heavy edge assigned phase `T`.

Every selected heavy edge is deleted in exactly one phase, so each physical heavy marginal becomes `(4/5)x_h`. At every star, selected heavy edges at its top four leaves have distinct deletion phases. The stars may be linked by heavy edges; the auxiliary coloring enforces the phase condition simultaneously.

## Prefix recourse and two count-gap bounds

For the prefix of the first `k` leaves of a star, write `Z_k` for their total selected heavy weight in the **full** matching, and `R_k=k−Z_k` for their raw residual total. Its fluid recourse is

`F_k(full)=min(1,R_k)`.

The mean-capacity benchmark is `F_k(D)=min(1,k−E Z_k)`. If `k>=4`, either one of the top four leaves was already heavy-free, in which case recourse is one in every phase, or all four were covered and their four distinct deletion phases each free a leaf. Therefore `E_T F_k(new)>=4/5>=(4/5)F_k(D)`. For `k=1`, the phase mean residual is `1−(4/5)L_1=1/5+(4/5)D_1>=(4/5)F_1(D)`.

For `k=2,3`, when all prefix leaves are covered, deleting any one of their distinct selected heavy edges frees a unit-capacity leaf and raises recourse to one; when at least one leaf was already free, full recourse was already one. Hence the **exact conditional identities** are

`E_T F_2(new)=2/5+(3/5)F_2(full)`,

`E_T F_3(new)=3/5+(2/5)F_3(full)`.  (2)

We need full-law Jensen gaps `C_k:=F_k(D)−E_M F_k(full)` of at most `1/3` for `k=2` and `1/2` for `k=3`.

**Two leaves.** Let `N` be the number covered in the top two, `P=E N`, `m=E Z_2`. If `P<=1`, (1) forces `N<=1`, so `Z_2<=1` always and `C_2=0`. If `P>=1`, (1) forces `N∈{1,2}`; set `a=Pr(N=2)=P−1`. Define `T=E(Z_2−1)_+`, so `E F_2(full)=1−T`. On `N=1`, the selected weight lies in `[1/2,1]`; on `N=2`, the total lies in `[1,2]`. Therefore `T<=a` and

`m >= (1/2)(1−a)+a+T = (1+a)/2+T`.  (3)

If `m<=1`, then `C_2=T<=min(a,(1−a)/2)<=1/3`. If `m>=1`, then `C_2=1−m+T`; (3) gives `C_2<=(1−a)/2`, while `T<=a` and `m>=1` give `C_2<=a`. Again `C_2<=1/3`.

**Three leaves.** Let `P=E N` for the top three and `m=E Z_3`. If `P<=2`, (1) forces `N<=2`, so some leaf is free in every full state, and `C_3=0`. If `P>=2`, (1) forces `N∈{2,3}`. Let `a=Pr(N=3,Z_3>2)` and `b=Pr(N=3,Z_3<=2)`, and put `T=E(Z_3−2)_+`. Then `T<=a`, and `E F_3(full)=1−T`. On the three disjoint events `(N=2)`, `(N=3,Z_3<=2)`, `(N=3,Z_3>2)`, respectively, the quantities `Z_3−(Z_3−2)_+` are at least `1`, `3/2`, and `2`. Thus

`m−T >= (1−a−b)+ (3/2)b+2a=1+a+b/2`.  (4)

If `m<=2`, then `C_3=T<=a` and (4) gives `C_3<=1−a−b/2`; hence `C_3<=1/2`. If `m>=2`, then `C_3=2−m+T<=a` and (4) again gives `C_3<=1−a−b/2`; hence `C_3<=1/2`.

Using (2), `C_2<=1/3`, `C_3<=1/2`, and `F_k(D)<=1` yields

`E F_2(new)>=2/5+(3/5)(F_2(D)−1/3)=1/5+(3/5)F_2(D)>=(4/5)F_2(D)`,

`E F_3(new)>=3/5+(2/5)(F_3(D)−1/2)=2/5+(2/5)F_3(D)>=(4/5)F_3(D)`.

All prefix recourse inequalities therefore hold simultaneously.

## Profit integration and hull inclusion

For one unheavy-centered fluid star with leaf profits `q_i`, the fractional-knapsack layer-cake identity is

`F_q(r)=∫_{λ>=0} min(1, Σ_{i:q_i>=λ} r_i) dλ`.

Its threshold sets are profit prefixes, so integrating the proven prefix inequalities gives `E F_q(new)>=(4/5)F_q(D)>=(4/5)q·y` on each star. The phase construction and balanced full heavy law work simultaneously across the vertex-disjoint star forest, and its fluid recourse values add. For every `q>=0`, a law with exact heavy marginals `(4/5)x` therefore offers fluid profit at least `(4/5)q·y`. Nonnegative-profit support-function separation yields a one-color mixed-state distribution with exact mean fluid vector `(4/5)y`.

The argument uses the heavy-free-center condition in every prefix formula. A heavy edge at a center makes its capacity random, and balancing top-two/top-three leaf coverage alone does not control that additional source. It also uses bipartiteness both for the laminar-quota network and for proper four-edge-coloring of the auxiliary graph.
