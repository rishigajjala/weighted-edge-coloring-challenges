# Mixed-rank guard hierarchy: targeted tests and a rank-transition barrier

**Status.** No unrestricted bipartite lower bound above `4/3` was found. The
finite-state results below are exact optimizations of the stated finite
transition models up to floating-point LP arithmetic; they are not theorems
about all weighted multigraphs.

## Two simultaneous graded path classes

The script `bipartite_mixed_rank_two_three_guard.py` enumerates every feasible
one-color state `(A_in,B_in,A_out,B_out,g_A,g_B)` for two path classes with
weights, in units of `1/6000`,

```
A_in=2501, A_out=2500, B_in=1601, B_out=1600,
g_A=3500=6000-A_out, g_B=2800=6000-2 B_out.
```

Thus `A` has local rank two and the heavy `A` guard fits one outgoing `A`
but no incoming `A`. The rank-three `B` guard fits two outgoing `B` but
not two incoming `B`. This provides two nested transition obstructions,
with mixed configurations retained rather than treated independently.

The local model balances only the *means* of the incoming/outgoing counts
for each class. The stationary global model balances their *full joint
count-state law* along the path. For every nonnegative profit on the four
types, `bipartite_mixed_rank_two_three_guard_exact.py` optimizes the
local/stationary ratio by enumerating all 119 local hull vertices and
solving the polar potential LP for each. The maximum is `4/3`, attained
with profits `(A,B,g_A,g_B)=(1,0,1,0)`: the second rank is discarded.
Reversing the direction of the `B` transition leaves the maximum `4/3`.
Moving both core types near the upper ends of their bands
(`A≈0.49`, `B≈0.332`) likewise gives `4/3` in both orientations. See the
`*_exact.log` files.

## A shared-rung ladder

The script `bipartite_shared_rung_ladder_stationary.py` instead puts one
physical guard on a ladder rung. It simultaneously guards rank-two rails
at its two endpoints, so the guard price is counted once and both rails
can impose incompatible incoming transitions. There are 40 local states
and 190 distinct local mean vertices. The exact local/stationary gauge is
again `4/3` for both aligned and opposed rail gradients. Every displayed
maximizer uses only one rail and the rung in its local mean;
the other rail is inactive.
The aligned-gradient case has the intended finite physical ladder
realization. With one shared rung weight at each position, the formal
opposed-gradient transition model need not be realizable on an
arbitrarily long physical ladder: keeping the same guard exactly at
both rail compatibility thresholds would require the rail weights to
move together. Its negative result is only an abstract diagnostic.

This specifically rejects the proposed amplification by reusing a heavy
guard as a guard for a second graded path at its other endpoint, at least
in the homogeneous stationary ladder model. It does not rule out
nonstationary bundles, branches, or a different physical coloring
obstruction.

There is also a direct geometric barrier when the two rails lie in
strictly separated rank bands. Suppose an `A` outgoing edge has weight
`a>1/3` and a `B` incoming edge has weight `b<1/3`, so `b<a`.
If the shared guard of weight `g` can pair with the `A` edge, then
`g<=1-a`. Hence `g+b<1`; the same guard cannot reject the incoming
rank-three `B` edge. Conversely a guard rejecting that `B` edge has
`g>1-b>1-a` and cannot pair with the `A` edge. One physical rung
therefore cannot simultaneously implement the complementary
guard/rejection transition for two separated ranks.

## Why a simple alternating-rank path loses its guard obstruction

At a path vertex, a guard complementary to an outgoing core edge of weight
`w_out` has weight `1-w_out`. It can be incompatible with an incoming edge
of weight `w_in` only if `w_in>w_out`. Thus when a path transitions from
rank two (`w>1/3`) to rank three (`w<1/3`), the transition can preserve
the rejection direction. A transition back to rank two necessarily has
`w_in<w_out` and its guard *accepts* the incoming edge. Consequently a
periodic rank-two/rank-three alternation cannot repeat the same
one-sided guard rejection at every vertex. Descending-size hierarchies
have only downward rank transitions along any root-to-leaf path, so a
naive stacking of the rank-two path obstruction cannot amplify its
`4/3` ratio by cycling between bands.

This is only a barrier to that particular complement-guard mechanism.
Shared noncomplementary guards, several core bundles meeting a vertex,
or constraints not captured by stationary profit/count laws may behave
differently. A viable higher-rank lower construction must keep a
positive rank-three **demand** at a ratio above `4/3`; the displayed
equality witnesses set that local demand to zero. A positive price
could still be assigned to an unused type without changing a witness.

## The 2:1 shared-guard resonance

The separated-band barrier does not cover a guard that pairs one rank-two
edge **or two rank-four edges**. For example, in units of `1/12000`, take
outgoing/incoming `A=(5760,5762)`, outgoing/incoming `B=(2880,2881)`,
and one shared guard of weight `6240`. Then guard plus one outgoing `A`
and guard plus two outgoing `B` each fit exactly; replacing those edges
by their incoming counterparts makes the load exceed one. This is a
genuine two-rank threshold resonance, not two independent guards.

`bipartite_resonant_rank_two_four_shared_guard.py` enumerates its 35
feasible local states. The full-profit exact-gauge diagnostic enumerates
all 104 local mean vertices. The stationary gap is again `4/3`, in
the aligned `B` orientation, with maximizing price
`(p_A,p_B,p_g)=(1,0,1)`. Thus even the resonant shared choice does not
amplify the path obstruction in this homogeneous model. The result
does not exclude other rank ratios, multiple interacting guards, or
finite nonstationary networks.

The `2:1` incoming and outgoing increments above ensure a physical
long-path realization: choose outgoing weights along the path with
`A_i=2B_i`, decrease `B_i` by an arbitrarily small amount each step,
and put the rung guard at `1-A_i=1-2B_i`. The threshold pattern is
exactly the enumerated one throughout any prescribed finite path
after choosing the decrement small enough. Opposing gradients cannot
keep both rails at the same shared-guard threshold for long, so that
orientation's LP result is only formal.

Putting these resonant `A` and `B` paths on two separate rails of a
ladder, with the same physical guard on each rung, does not change the
result. The updated `bipartite_shared_rung_ladder_stationary.py` with
`RESONANT_LADDER=1` has 98 feasible local states and 1,693 distinct
local mean vertices. The exact stationary gauge remains `4/3` for
the physically aligned rail orientation, with `B` demand zero in the
displayed maximizing local mean. This is the direct physical-rung version
of the proposed rank-two/rank-four guard hierarchy.
