# A physical XOR phase gadget, and why its balanced point stays at 4/3

This is an exact obstruction to a specific proposed lower-bound point,
not a bound for arbitrary demands or arbitrary factors.

Make a bipartite network of hub factors. Each factor has three port
vertices joined to a private hub by a unit-weight `A` edge of profit
2 and two weight-`1/2` edges `B,C` of profit 1 each. Each port is
incident to one unit-weight blocker edge; blockers form a matching
between ports of distinct factors. Connect factors of opposite
bipartite orientation, so the entire physical graph remains
bipartite. A blocker is incompatible with the spoke at either of its
ports, regardless of whether it connects A-to-A, B-to-B, or A-to-B.
Thus same-weight blockers can join different local *roles*.

At each factor the maximum spoke profit is 2, attained either by
selecting `A` alone or by selecting both `B,C`. Calling those two
factor phases 0 and 1, the saturated local pattern laws are

    phase 0: (blocker states at A,B,C) = (0,1,1),
    phase 1: (blocker states at A,B,C) = (1,0,0).

A shared blocker enforces equality of its physical state at both
endpoints. An A-to-B connection therefore relates factor phase labels
with a sign flip; A-to-A and B-to-B connections preserve the label.
Odd signed cycles in the factor network can make all factors' phase
constraints jointly unsatisfiable, even though the physical graph is
bipartite. This is a real role-twist mechanism rather than a simple
graded path.

Nevertheless, take the natural balanced local point: each factor
mixes its two spoke phases 50/50, and every blocker has local mean
`1/2`. If there are `n` factors and the sum of all blocker profits is
`P>=0`, its local objective is exactly

    L = 2*n + P/2.

Select every physical blocker independently with probability 1/2,
and independently optimize spokes in each factor conditional on its
three blocker states. If A is free (probability 1/2), its profit 2 is
available. If A is blocked, the two half-weight spokes together earn
the number of them whose blockers are free, with expectation 1.
Therefore each factor's conditional expected spoke profit is at least

    (1/2)*2 + (1/2)*1 = 3/2.

Blocker profit has expectation `P/2`, so some feasible physical color
has profit at least

    M >= 3*n/2 + P/2.

Consequently the proposed balanced point satisfies

    L/M <= (2*n+P/2)/(3*n/2+P/2) <= 4/3.

The signed phase constraints are genuinely frustrated, but their
unsatisfied-pattern loss cannot push *this* point beyond the existing
bipartite `4/3` lower bound. More than two balanced local packing
phases or a different profit/demand profile would be needed.
