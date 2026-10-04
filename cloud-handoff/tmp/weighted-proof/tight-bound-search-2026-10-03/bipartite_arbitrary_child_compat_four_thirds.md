# Exact 4/3 coloring for rooted forests with arbitrary guard-child compatibility

**Independent research note; not part of the main manuscript.**

## Theorem

Let a loopless weighted multigraph have a rooted-forest core after parallel bundles are suppressed. Every physical core edge has weight in `(1/3,1/2]`; weights of parallel edges may differ. Each further edge joins a core vertex to its own private leaf and has weight greater than `1/2`; call it a guard. At each nonroot core vertex, assume **every** guard is incompatible with **every** physical edge of its parent bundle, so the two weights sum to more than one. A guard may or may not fit a child edge, independently of other guards and child edges.

If `B=bp(G)`, then

    chi'_w(G) <= ceil(4B/3).                         (1)

An explicit physical-edge coloring can be constructed in polynomial time. The upper coefficient is sharp in this class because the existing graded path with leaves satisfies these assumptions and has ratio `4/3`.

The prior theorem `rooted-compatible-guards-four-thirds.tex` assumed each guard fits **every** child edge. The proof below removes that assumption. It does not require uniform weights within a parallel core bundle.

For a concrete vertex profile covered here but not by that prior hypothesis, take an incoming core edge of weight `0.45`, one guard of weight `0.60`, and outgoing core edges of weights `0.35` and `0.42`. The guard is incompatible with its parent edge, fits the first child edge, and is incompatible with the second child edge.

## Exact local bin count

Fix a core vertex `v`. Let `g` be its number of guards, let `d_e` be the number of physical edges in each incident core bundle, and put `T=sum_e d_e`. Construct the bipartite compatibility graph between its guards and its outgoing core edges. Let `q` be a maximum matching size. At a root there is no parent bundle; at other vertices no guard can pair with a parent edge by assumption.

Every local packing uses one separate bin per guard and can pair guards with at most `q` core edges. All remaining core edges require at least `ceil((T-q)/2)` additional bins, since every core edge weighs more than `1/3`. Conversely, pair the `q` matched guard-child edges and pair the remaining core edges arbitrarily; every two core edges fit because each weighs at most `1/2`. Therefore

    b_v = g + ceil((T-q)/2),
    2B >= 2g+T-q.                                   (2)

The private leaf constraints are automatically no larger than the bound at the core endpoint. The maximum matching is computable in polynomial time.

For each child bundle `e`, fix one maximum matching at its parent and let `q_e` be the number of its matched physical edges. Thus `q=sum_child q_e`. At a parent bundle viewed from its child, set its local `q_e=0`. Notice `q<=g`, `q<=T`, and, for every incident bundle `e`, `q-q_e<=T-d_e`.

## Common physical states on every core bundle

For each core bundle `e` of size `d_e`, globally record

    t_e=floor(d_e/3) disjoint pairs of physical edges,
    s_e=d_e-2t_e remaining physical singleton edges. (3)

Make this choice at the **parent** endpoint. Of the `q_e` physical edges matched to guards there, retain `r_e=ceil(q_e/3)` among the singletons. This is possible because `s_e>=ceil(d_e/3)>=ceil(q_e/3)`. Choose the other singletons arbitrarily, and pair all remaining edges arbitrarily. The same recorded pairs and singleton labels are used at the child endpoint. Every recorded pair fits in one bin at either endpoint, even when its two physical weights differ.

## A local list of `K=ceil(4B/3)` bins

Fix `v` again. Put each recorded core pair incident to `v` in its own bin. Write `D=sum_e t_e` for these bins and `S=sum_e s_e=T-2D` for the remaining core singletons. For every outgoing bundle `e`, take its `r_e` recorded singletons that were matched to guards and pair them with their original distinct compatible guards. Set `r=sum_child r_e`; leave the other `g-r` guards alone. At the parent bundle, put local `r_e=0` because no guard at `v` is compatible with it.

Only core singletons remain to be packed. Give bundle `e` a part of size `a_e=s_e-r_e`. Pair items from **different** parts whenever possible. Any such pair fits. The minimum bin count for a complete multipartite pairing is

    max{ max_e a_e, ceil((S-r)/2) }.                (4)

To see (4), a largest part cannot pair internally, and every bin holds at most two items. Conversely, if one part has at least half the items, pair every item outside it with a distinct item inside it. Otherwise, when the total is odd set one item aside, arrange the remaining parts consecutively, and pair position `i` in the first half of that list with position `i` in the second half. Each contiguous part has length at most half the retained list, while paired positions differ by exactly that half, so no pair has both members in one part.

Consequently the local construction uses

    D+g+max{ max_e(s_e-r_e), ceil((S-r)/2) }         (5)

bins. We check each term is at most `K`.

### The total singleton term

Since `r_e>=q_e/3`, we have `r>=q/3`. Also `D+S/2=T/2`, so

    D+g+ceil((S-r)/2)
      =ceil(g+T/2-r/2)
      <=ceil(g+T/2-q/6).

Equation (2) gives `4B/3>=4g/3+2(T-q)/3`, and

    4g/3+2(T-q)/3 - (g+T/2-q/6)
      =(2g+T-3q)/6 >=0,

because `q<=g,T`. The total singleton term is therefore at most `K`.

### Every largest-part term

For every incident bundle `e`, (2) yields

    4B-(3g+T+d_e-q_e)
      >= g+T-d_e-2q+q_e
      =(g-q)+(T-d_e-(q-q_e)) >=0.                 (6)

Here `q_e=0` for the parent bundle. Define rounding residues

    delta_e=d_e/3-floor(d_e/3) in {0,1/3,2/3},
    epsilon_e=ceil(q_e/3)-q_e/3 in {0,1/3,2/3}.

Equations (3) give `D=T/3-sum_f delta_f` and `s_e=d_e/3+2delta_e`. Hence

    D+g+s_e-r_e
      =g+(T+d_e-q_e)/3
       +delta_e-sum_{f!=e}delta_f-epsilon_e
      <4B/3+1                                           (7)

by (6). The left side is an integer, so it is at most `ceil(4B/3)=K`. This proves (5) is at most `K` and permits empty padding to exactly `K` bins at every core vertex.

## Glue the local lists through the forest

Each core bundle has exactly the same physical states at its two endpoints: its `t_e` recorded two-edge subsets, its `s_e` recorded singleton edges, and empty states elsewhere in the local lists. Root each tree and permute the *entire* list at each child to make these bundle states coincide with its parent's list. Continue outward. Such a permutation does not disturb an already matched parent bundle and affects only unprocessed child bundles. Each guard inherits the color of its bin at the core endpoint; its private leaf imposes no additional conflict. The result colors every physical edge exactly once and is feasible at all vertices, proving (1).

The matching choices, pair selections, multipartite pairings, and tree permutations are polynomial in the explicit physical edge list.

## Scope and consequence

The theorem rules out a bipartite lower coefficient above `4/3` from any rooted-forest core of medium edges with private heavy guards that are incompatible with their incoming core edges, even if compatibility with child edges varies arbitrarily across physical weights. It does not cover guard compatibility with incoming edges, multiple incoming bundles at a vertex, non-forest cores, core edges of weight at most `1/3`, or additional edges between guard leaves.

The same proof gives the corresponding fractional profit-hull statement: for a fixed typed rooted-forest support in this class, the global repeatable-count configuration hull contains `3/4` of the intersection of the local integer knapsack hulls. For rational local-hull point `x`, choose an integer `N` divisible by three that clears the coefficients of every local configuration decomposition. Realize `Nx_e` physical copies of each type, locally pack them in `N` bins, and apply the theorem to color them in at most `4N/3` colors. A uniformly chosen color has expected type-count vector `3x/4` after empty padding. Closure extends to real `x`. This consequence concerns unbounded count patterns, whereas the theorem above colors the original physical edges exactly once.

As an arithmetic diagnostic, a pure-Python exhaustive check verified inequality (5) against `K` for 22,336 profiles with three incident core bundles, each bundle count at most six, at most seven guards, and all feasible matching-count splits. The independent proof audit is recorded separately by the general-lower research agent. This finite check supplements the symbolic inequalities; it is not used in the proof.
