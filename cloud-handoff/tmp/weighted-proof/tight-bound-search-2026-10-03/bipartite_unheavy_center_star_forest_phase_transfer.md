# Interim: four-phase transfer for a bipartite fluid star forest

Status: audited intermediate theorem under the five-hour instruction; no claim about unrestricted weighted edge coloring. This note concerns a local convex-hull inclusion for categorical heavy edges and uncapped divisible fluid edges.

## Model and statement

Let the combined multigraph be bipartite. Categorical edge types `h` have arbitrary weights `w_h in [0,1]`, including heterogeneous weights and parallel types; they are required to form a matching in each one-color state. Their local marginals `x_h>=0` satisfy `sum_{h incident v}x_h<=1` at every vertex. The physical heavy-edge case is the subrange `w_h>1/2`, where this matching condition is automatic. Fluid edges have target loads `y_e>=0` and no edge supply caps; they satisfy

`sum_{h incident v}w_h x_h + sum_{e incident v}y_e <=1`

at every vertex. Suppose the fluid support is a vertex-disjoint star forest and **no fluid-star center is incident to a heavy edge**. The heavy support is otherwise arbitrary, including links between leaves of different fluid stars. Then the target heavy marginals `(3/4)x_h` and fluid load means `(3/4)y_e` belong to the convex hull of one-color feasible mixed states. The heavy state in one color is a matching; conditional fluid loads obey the residual vertex capacities after its heavy edges are selected.

The proof proceeds by support functions. Fix any nonnegative fluid profit vector `q`. It suffices to construct a heavy matching law with marginals `(3/4)x_h` whose expected optimal fluid recourse has profit at least `(3/4)q·y`. The law may depend on `q`, because separation over the convex expected fluid-feasible set then gives one law for all edge coordinates. Negative profits cause no additional inequalities because fluid feasible sets are downward closed.

## Simultaneous phase coloring

By bipartite matching-polytope integrality, choose **any** distribution of full heavy matchings `M` with edge marginals `x_h`. Within each fluid star, order the leaves `v_1,v_2,...` by decreasing `q` (ties arbitrary). Conditional on a selected full matching `M`, create an auxiliary multigraph with one vertex for each fluid star. For each selected heavy edge incident to a top-three leaf of a star, represent it by an auxiliary edge: join the two relevant star vertices if the heavy edge is incident to top-three leaves at both ends, or join the relevant star vertex to a fresh private dummy vertex if only one end is relevant. A heavy edge cannot have both ends as leaves of the same fluid star, since those leaves lie on one shore of the original bipartition. When it joins leaves of two stars, those stars' centers are on opposite shores. Therefore the auxiliary graph is bipartite. A full heavy matching covers at most the top three leaves of each star, so the auxiliary maximum degree is at most three, even allowing parallel edges. Properly color its edges with colors `1,2,3` by bipartite multigraph edge-coloring. Assign color `4` to every selected heavy edge with no top-three-leaf incidence.

Draw one **global** uniform phase `T in {1,2,3,4}` and delete precisely the selected heavy edges of color `T`. A subset of a matching is a matching. Each originally selected heavy edge is deleted in exactly one of four equally likely phases, regardless of how the conditional edge-coloring was chosen. Hence every heavy edge has final marginal `(3/4)x_h`. At each star, the selected heavy edges covering its top three profit-ranked leaves, if present, have pairwise distinct phase colors.

## Prefix recourse calculation at one star

Its center has capacity one in every heavy state. For a profit prefix `P_k={v_1,...,v_k}`, let `R_i` be the physical residual capacity at leaf `v_i` after phase deletion, and let `L_k=sum_{i<=k}sum_{h incident v_i}w_hx_h`. The unit-profit prefix recourse is

`f_k(R)=min(1,sum_{i<=k}R_i)`.

The corresponding local fractional optimum is `f_k(D)=min(1,k-L_k)`, where `D_i=1-sum_{h incident v_i}w_hx_h`.

* For `k>=3`: If a top-three leaf was originally unmatched, it remains fully free. Otherwise its three heavy edges have three distinct colors, so three of the four phases delete one of them. Thus `E f_k(R)>=3/4 >=(3/4)f_k(D)`.
* For `k=1`: Every selected heavy edge at `v_1` survives with probability `3/4`, so `E f_1(R)=1-(3/4)L_1=1/4+(3/4)D_1 >=(3/4)f_1(D)`.
* For `k=2`: If either leaf was originally unmatched, the prefix recourse is one for all phases. If both were matched by heavy edges of weights `w_1,w_2`, their edges have distinct colors; two phases delete one of these edges and give recourse one, and two phases retain both and give `1-(w_1+w_2-1)_+`. Since `(W-1)_+<=W/2` for `W in[0,2]`, averaging over phases and full matchings gives `E f_2(R)>=1-L_2/4`. If `L_2<=1`, the right side is at least `3/4`; if `L_2>=1`, it is at least `(3/4)(2-L_2)`. Therefore `E f_2(R)>=(3/4)f_2(D)` in all cases.

For an uncapped star with center capacity one, its arbitrary-profit fractional-knapsack value has the exact layer-cake formula

`F_q(R)=integral_{lambda>=0} min(1,sum_{i:q_i>=lambda}R_i) d lambda`.

The threshold leaf sets are ordered prefixes. Integrating the three prefix estimates yields `E F_q(R)>=(3/4)F_q(D)` at each star. Because the fluid stars have disjoint vertex sets, their optimal recourse values add under every heavy state. Summing yields `E F_q(R)>=(3/4)F_q(D)>=(3/4)q·y` globally. The heavy marginals stay `(3/4)x` independently of `q`; support-function separation proves the stated local-hull inclusion.

## Exact limits

The center-free condition is used in the prefix identity and in the k=1,2 estimates. If a star center is heavy, prefixes of length at least three still satisfy the `(3/4)` inequality under this phase construction (a fully free leaf makes prefix recourse equal the current center residual), but k=1 and k=2 require a suitable heavy matching coupling. An arbitrary full matching law can fail already at k=1: two disjoint unit-heavy edges with unscaled marginals `1/2`, chosen anticorrelated, and a fluid edge joining opposite-shore endpoints have local target `1/2`; independent `3/4` thinning leaves availability `1/4`, below the target `3/8`. Nor does this proof handle fluid-forest components that are not stars, or fluid edge supply caps.
