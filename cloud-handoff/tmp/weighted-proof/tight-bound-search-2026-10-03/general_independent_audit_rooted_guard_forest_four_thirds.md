# Independent audit: rooted guarded forest has an exact ceil(4B/3) coloring

This audits the construction supplied by the bipartite lower-bound agent
on 3 October 2026. **Verdict: valid under the scope below.** It is a
restricted coloring theorem, not the unrestricted bipartite 3/2 theorem.

## Precise scope

The simple core support is a rooted forest. Parallel physical core edges
in each parent-child bundle may have arbitrary, individually varying
weights in `(1/3,1/2]`. Every core vertex has any number of private
guard edges to leaves, each with weight in `(1/2,1]`. Every guard at a
core vertex is incompatible with every edge of that vertex's parent
bundle; compatibility with outgoing child-bundle edges is arbitrary.
Set `B=bp(G)`, the maximum exact vertex bin-packing number. Then

    chi'_w(G) <= ceil(4B/3).                             (1)

No common weight within a bundle, divisible items, or asymptotic
rounding is assumed.

## Exact local packing number

Fix a core vertex `v`. Write `d_e` for the physical item count in
each incident core bundle, `T=sum_e d_e`, and `g` for its guard count.
Let `q` be the cardinality of a maximum bipartite matching between the
`g` physical guards and compatible physical edges in outgoing bundles.
Every guard needs its own bin and can contain at most one outgoing
core edge. It cannot contain an incoming edge. If a packing uses `r`
such guard-core pairs, then its other `T-r` core edges need at least
`ceil((T-r)/2)` bins because three core edges weigh more than one.
Thus it uses at least `g+ceil((T-q)/2)` bins. Conversely, realize a
maximum matching of size `q`, put the matched pairs in guard bins,
and arbitrarily pair all remaining core edges. Any two core edges
fit because each weighs at most `1/2`. Hence the exact local minimum is

    b_v = g + ceil((T-q)/2) <= B.                        (2)

For each outgoing bundle `e`, let `q_e` be the number of matched edges
in that bundle; put `q_e=0` on the incoming bundle. Thus
`sum_e q_e=q`, `q<=g`, and `q_e<=d_e`.

## A common physical partition on each bundle

For every oriented core bundle `e`, its parent chooses

    t_e=floor(d_e/3) disjoint physical pairs,
    s_e=d_e-2t_e physical singletons.

It requires `q'_e=ceil(q_e/3)` of its matched outgoing physical edges
to be among the singletons. This is possible: `s_e>=ceil(d_e/3)` and
`q'_e<=ceil(d_e/3)`. The chosen matched edges retain their distinct
guards. Both endpoints use **the same physical pairs and singletons**.
At a child the incoming bundle has local `q_e=q'_e=0`; this does not
alter its partition.

At `v`, place each core pair alone in a bin, put the `q'=sum_e q'_e`
retained guard-singleton matches in their guard bins, and give each
remaining guard its own bin. The remaining core singletons must be
paired across different bundles to preserve the bundle-state
partition. If `a_e=s_e-q'_e` and `S=sum_e s_e`, their minimum number of
bins is

    max(max_e a_e, ceil((S-q')/2)).                      (3)

The formula is the standard complete-multipartite pairing count:
one needs at least the largest part size and half the total rounded
up. To attain it, if the largest part has at least half the items,
pair every item outside it with a distinct item inside it. Otherwise,
when the total is odd, set aside one item; concatenate the remaining
parts and pair positions separated by half the list length. No part
has more than half the remaining items, so such positions cannot lie
in the same part. Any such two core items fit. Thus the construction
uses at most

    D+g+max(max_e a_e,ceil((S-q')/2)),                   (4)

where `D=sum_e t_e`.

## Audit of both integer bounds

First, `D+g+ceil((S-q')/2)=ceil(g+T/2-q'/2)`. Since
`q'=sum_e ceil(q_e/3)>=q/3`, (2) gives

    4B/3-(g+T/2-q/6)
       >= (2g+T-3q)/6 >= 0,                            (5)

because `q<=g` and `q<=T`. Therefore the total-singleton term in
(4) is at most `K=ceil(4B/3)`.

For a fixed bundle `e`, (2) implies

    4B >= 4g+2(T-q)
       >= 3g+T+d_e-q_e.                                (6)

The second difference is `(g-q)+(T-d_e-(q-q_e))`, both nonnegative:
the `q-q_e` matched edges lie outside bundle `e`.

Write `delta_e=d_e/3-floor(d_e/3)` and
`epsilon_e=ceil(q_e/3)-q_e/3`. Direct expansion gives

    D+g+s_e-q'_e
      = g+(T+d_e-q_e)/3
        +delta_e-sum_(f!=e)delta_f-epsilon_e
      < 4B/3+1.                                        (7)

The left side is an integer, so it is at most `ceil(4B/3)=K`, including
when `4B/3` is integral. Equations (5)--(7) bound (4) by `K`.

## Tree gluing and physical feasibility

Pad every core vertex's constructed list to `K` bins. On each
parent-child bundle, both endpoint lists contain exactly the same
multiset of states: the same `t_e` two-edge physical subsets, the same
`s_e` physical singleton subsets, and `K-t_e-s_e` empty states.
Root the core forest; label the root bins with the `K` colors and
permutate each child's entire bin list to match its parent's states
on their shared bundle. There is only one previously fixed neighbor
at each child, so this introduces no conflict. A guard edge inherits
the color of its core-endpoint bin; its private leaf has no other
constraint. Every color is then a well-defined subset of original
physical edges and is feasible at every vertex. This proves (1).

The key rounding checks are `q'_e<=s_e` and the strict `<4B/3+1`
in (7). Replacing either by a real-valued approximation would leave a
possible one-color gap; both hold exactly for physical integer counts.
