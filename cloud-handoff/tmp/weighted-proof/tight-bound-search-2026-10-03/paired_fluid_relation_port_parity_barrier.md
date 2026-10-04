# Port-parity barrier to a simple blocker-correlation frustration cycle

This is a combinatorial restriction on a proposed paired-heavy plus
divisible-fluid lower gadget. It is **not** a bound on its coloring gap.

Contract every heavy matching edge to one blocker vertex, retaining
its two physical ports `L_i` and `R_i`. A direct fluid edge between
two blocker pairs joins opposite-side ports. A two-spoke fluid star
with a fixed hub and leaves at two blocker pairs joins same-side
ports. These two gadgets can favor opposite correlations of the
heavy states: a direct bottleneck benefits from simultaneous free
states, whereas two competing spokes can benefit from dispersed free
states. The preference language is heuristic and depends on the
chosen demands/profits; the port assertion below is exact.

Suppose a cycle of pairwise relation gadgets visits each blocker
through **distinct** ports on its two incident relations. Let a direct
relation have parity one, because its endpoint ports are on opposite
bipartition sides, and a same-hub two-spoke relation have parity zero,
because its leaf ports are on the same side. At every blocker along
the cycle, moving between the ports flips the side bit. The total
side-bit change around a closed cycle is zero, so

    (# direct relations) + (# blocker port flips) = 0 mod 2.

There is one port flip per blocker; for a cycle of length `k`, this
gives `#direct = k mod 2`, or equivalently **an even number of
same-hub relations**. Therefore an odd cycle of the putative
negative-correlation relations cannot be realized with every blocker
using one port per relation. It must reuse a port somewhere, causing
the incident fluid gadgets to compete for that physical endpoint's
capacity, or use a more complex relation than these two primitives.

The exact-state LP diagnostic `paired_fluid_three_pair_c6_gauge.py`
is consistent with this barrier: on the three-pair off-diagonal C6
fluid support, all vertices of the local mean polytope were checked
for 56 symmetric weight triples from
`{.5001,.55,.6,.7,.8,1}`; the largest observed gap was `5/4`, always
realized by a single direct fluid edge and two blockers. On four and
five pair dense off-diagonal supports, sampled local vertices also
did not exceed `5/4`. These computations are finite diagnostics, not
proof of a universal `5/4` bound.
