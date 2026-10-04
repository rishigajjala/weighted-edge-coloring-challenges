# Unequal-demand graded guard paths: a four-thirds ceiling bound

**Interim research status (five-hour exploration protocol).** The argument below has been independently audited by the parent agent, but is a scoped scratch result, not a new unrestricted claim or a manuscript change. It is a coloring bound for one physical bipartite path-with-private-guards family, allowing arbitrary core-bundle multiplicities and arbitrarily many rank changes. The finite bound has the ceiling `ceil(4B/3)`; it does **not** imply `chi/B <= 4/3` for every small instance. For example, the two-core profile `(2,1)` can have `B=2`, `chi=3`.

Take a path `v_0,...,v_m`. Core bundle `i` between `v_i,v_{i+1}` consists of `d_i>=1` equal-weight physical edges of weight `w_i` with `0<w_i<1/2`. At `v_i` for `i<m`, attach `d_i` private-leaf guards of weight `1-w_i`. At the terminal `v_m`, attach any number `h>=0` of private guards that reject every incoming core edge. Assume `w_0>w_1>...>w_{m-1}`; this ensures each nonroot guard rejects the preceding incoming bundle. Put `k_i=floor(1/w_i)>=2` and `q_i=ceil(d_i/k_i)`. Let `B=bp(G)`.

The exact local bin numbers are `b(v_0)=d_0`, `b(v_i)=d_i+q_{i-1}` for `0<i<m`, and `b(v_m)=h+q_{m-1}`. At an interior vertex the `d_i` guards occupy distinct bins and reject all incoming core edges, so the incoming bundle needs `q_{i-1}` additional bins. This is attained by pairing each outgoing core edge with one of its guards and packing the incoming edges in `q_{i-1}` bins. The endpoint formulas follow similarly. Thus `B` is the maximum of these explicit values.

**Theorem.** Every such physical graph has a coloring with `M=ceil(4B/3)` colors, for all integer multiplicities `d_i` and all decreasing weights described above.

Color forward along the path. At vertex `v_i`, suppose the incoming core bundle uses `c_{i-1}` distinct colors, with `c_{-1}=0`. Use `d_i` colors not occupied by that incoming bundle for the guards. Write

    t_i = M-d_i-c_{i-1}.

These are colors used by neither the incoming bundle nor a guard at `v_i`. Put up to `k_i` outgoing core edges in each of these free colors. Pair every remaining outgoing edge with a different guard color, one per color. This is physically feasible: `k_i*w_i<=1` and `(1-w_i)+w_i=1`. The number of distinct outgoing colors needed by this greedy choice is

    c_i = max(q_i, d_i-(k_i-1)t_i).                         (1)

We prove inductively the occupancy invariant

    c_i <= ceil(4q_i/3).                                  (2)

Assume (2) for the preceding bundle, with `q_{-1}=0`. The local bin bound gives `B>=d_i+q_{i-1}` (at the root, `B>=d_0`). Since `M=ceil(4B/3)`, elementary ceiling arithmetic gives

    t_i >= ceil(4(d_i+q_{i-1})/3)-d_i-ceil(4q_{i-1}/3)
        >= floor(d_i/3).                                  (3)

In particular the guard colors exist. Put `a=floor(d_i/3)`, so (1) and (3) give `c_i<=max(q_i,d_i-(k_i-1)a)`.

* If `k_i=2`, the second term is `d_i-a=ceil(2d_i/3)<=ceil(4q_i/3)` because `q_i>=d_i/2`.
* If `k_i=3`, write `d_i=3a+r`, `r=0,1,2`. The second term is `a+r`, which is at most `q_i` for `r=0,1`, and equals `q_i+1<=ceil(4q_i/3)` for `r=2`.
* If `k_i>=4`, the second term is at most `r<=2<=ceil(4q_i/3)` because `q_i>=1`.

This proves (2). At the terminal vertex, `B>=h+q_{m-1}`, hence `M-h>=ceil(4q_{m-1}/3)>=c_{m-1}`. Its guards can all be placed outside the incoming core colors. The resulting colors agree on every physical core edge because each outgoing bundle's colors are fixed at its parent and simply inherited by its child.

The proof only uses the incompatibility with incoming guards to establish the local `B` inequalities. The forward coloring itself does not require monotone weights; the compatible outgoing guard pair and per-bundle rank `k_i` suffice. Consequently it rules out an asymptotic lower gap above `4/3` from **every** unequal-demand, arbitrarily rank-changing, strictly descending complementary-guard path of this form. It does not address branching, nonprivate/shared guards, cycles, or edges with unequal weights within a bundle.

The `B=2`, `chi=3` example illustrates the ceiling caveat: take `d_0=2,d_1=1`, `w_0=2/5,w_1=3/10`, guards `3/5` at `v_0`, `7/10` at `v_1`, and a terminal guard of weight `1` at `v_2`. A two-coloring forces the two `2/5` core edges into different colors at `v_0`, leaving no color for the `7/10` guard at `v_1`; three colors suffice. Upon scaling all multiplicities, this particular obstruction tends to `5/4`, not `3/2`.

## Branching extension with full guard-child matching

The same proof covers a rooted-forest core with arbitrary branching. Each parallel parent/child core bundle `e` has `d_e` equal-weight edges of weight `w_e<=1/2`, and `k_e=floor(1/w_e)>=2`, `q_e=ceil(d_e/k_e)`. At each core vertex `v`, let `g_v` private guards each have weight greater than `1/2`. Every guard at a nonroot vertex rejects every incoming parent-bundle edge. Assume there is an injective assignment of **every outgoing physical core edge** to a different guard at `v` with which it is compatible. Thus `g_v>=sum_child d_e`. The weights need not decrease globally if the incompatibility hypothesis is checked directly.

Then `b_v=g_v+q_parent` at nonroots and `b_v=g_v` at roots: guard bins are mandatory and incompatible with incoming edges; all outgoing edges are paired with their assigned guards, and incoming edges occupy `q_parent` bins. Let `B=max_v b_v`, `M=ceil(4B/3)`. Suppose the parent bundle at `v` occupies at most `ceil(4q_parent/3)` colors. Place all `g_v` guards outside its support. The same ceiling arithmetic as (3) leaves at least `floor(g_v/3)` colors used by neither guards nor parent bundle. For each child bundle `e`, reserve `floor(d_e/3)` separate such free colors. This is possible because

    sum_child floor(d_e/3)
      <= floor((sum_child d_e)/3)
      <= floor(g_v/3).

Pack up to `k_e` edges of bundle `e` in each reserved free color. Pair all remaining edges of `e` with their individually assigned guards. Distinct child bundles use distinct reserved free colors and distinct matched guard colors, so this is a valid local coloring. Formula (1), with `t_i` replaced by the reserved `floor(d_e/3)`, and the same three rank cases show that child bundle `e` occupies at most `ceil(4q_e/3)` colors. Its child endpoint inherits those colors. Induction from roots colors the forest in at most `M` colors.

This branching extension is narrower than the known rank-two forest theorem with arbitrary guard-child compatibility, but it admits core weights below `1/3` and arbitrary nonuniform bundle multiplicities. It rules out an asymptotic coefficient above `4/3` from all such full-matching branching guard constructions.
