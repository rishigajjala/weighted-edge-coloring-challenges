# Heterogeneous heavy path: a bad local pipage law and a repairing long-range coupling

4 October 2026. This is an exact diagnostic for a proposed capped bipartite heavy-rounding method, not a counterexample to a hull inclusion.

Take the heavy path `0--1--2--3--4` with physical edge types `e_0,...,e_3`. Its edge weights are `w_0=w_3=1`, `w_1=1/2`, and arbitrary `w_2∈[1/2,1]`. The local heavy matching vector is

`x=(1/3,2/3,1/3,2/3) = (1/3)1_{M_0}+(2/3)1_{M_1}`,

where `M_0={e_0,e_2}` and `M_1={e_1,e_3}`. Add one divisible fluid chord `1--4` with target `y=1/3`; the combined graph is bipartite. Both chord endpoints have local heavy load `2/3`, so the local chord target saturates both residuals. Give the chord profit one and cap `C≥4=12y` (its effective cap is one because of vertex capacities).

At scale `alpha=3/4`, start heavy pipage rounding at `z=alpha x=(1/4,1/2,1/4,1/2)`. Independent binary vertex activation probabilities at the chord endpoints are `p_1=p_4=1/2`, giving multilinear recourse `Φ(z)=p_1p_4=1/4=alpha y` exactly.

Perturb the four path edges with signs `(+,-,+,-)`. The maximal positive step is `t_+=1/2`, and the maximal negative step is `t_-=-1/4`. Barycentric rounding selects them with probabilities `1/3,2/3` respectively. They produce

`z^+=(3/4,0,3/4,0)`, with `Φ(z^+)=1/4`, and

`z^-=(0,3/4,0,3/4)`, with `Φ(z^-)= (1−(3/4)(1/2))(1−3/4)=5/32`.

Thus `EΦ=(1/3)(1/4)+(2/3)(5/32)=3/16`, a drop of `1/16` below the target. The unequal heavy weights make the internal weighted loads change, so the common-weight alternating-path convexity argument does not apply.

If the two remaining disjoint fractional edges in each branch are rounded independently, the final expected actual chord recourse remains `3/16`; this valid heavy matching law misses the required `1/4` fluid target. There is no hidden residual-concavity gain on those final states that repairs it.

The same first path step *can* be repaired by correlating the two surviving edges in each branch: select both with probability `3/4`, neither with probability `1/4`. Each branch then gives expected chord recourse `1/4`. Overall the law is `M_0` with probability `1/4`, `M_1` with probability `1/2`, and the empty heavy matching with probability `1/4`. Its heavy marginals are exactly `z`, and the chord recourse is exactly `1/4`. In every final state of this repairing law, `F(R)=Φ(R)` on the chord: both nonempty matchings block one chord endpoint completely, and the empty matching frees both. The repair therefore comes from correlation between H edges that became disconnected after the first pipage step, not from Jensen slack between actual real residuals and binary vertex activation.

This example falsifies the claim that an arbitrary unbiased alternating-path rounding of heterogeneous heavy edges is recourse-nondecreasing. It leaves open whether a q-independent globally correlated heavy law always exists with the capped `3/4` target, and whether any such law has bounded local dependence suitable for a physical finite palette.
