# Interim audit: activation with finite edge supplies

Session status: still within the user's five-hour exploration period.
This is an internal candidate argument and audit record, not a claim that
the unrestricted coloring problem is solved.

## Candidate statement

Let G be a finite loopless multigraph, let 0 <= D_v <= 1, and let y >= 0
have incident load at most D_v. Let q >= 0 be edge profits and C >= 12y
be per-edge flow limits. Independently activate vertex v with probability
p_v = 1/4 + 3D_v/4. Write F_q(r,C) for the maximum q-profit fractional
edge flow with vertex capacities r and edge limits C. The candidate is

    E F_q(1_A,C) >= (3/4) q.y.

The graph need not be bipartite in this statement. The later transfer
from categorical physical heavy edges does still require bipartiteness
of the combined graph in the currently audited argument.

## Root audit of the bipartite proof

On a forest, delete a leaf edge uv with target a=y_uv. Reduce D_u by a,
and condition on every activation other than u,v. Let f(t) be the reduced
recourse with u-capacity t, A=f(0), and B=f(1)-f(0). The function f is
concave and nondecreasing. Put c=min(1,C_uv); use c, not C_uv, when
evaluating f(1-c). Concavity gives f(1-c)>=f(1)-cB. The gain from an
active leaf is therefore at least c(q_uv-B)_+.

Compared with the reduced activation law, the conditional expected gain
is at least (3a/4)B + p_u p_v c(q_uv-B)_+. If c<1, C_uv>=12a and
p_up_v>=1/16 give p_up_v c>=3a/4. If c=1, use

    (1/4+3a/4)^2 - 3a/4 = (3a/4-1/4)^2 >= 0.

The expected gain is at least 3a q_uv/4. Induction applies.

For arbitrary bipartite support, decompose y into extreme points y^k
of the unbounded degree polytope {z>=0:Az<=D}. Each positive support is
a forest. Use temporary caps C^k=12y^k. These caps can exceed C in an
individual component; their mean is 12y<=C. The activation law is the
same for every component because D is fixed. Monotonicity and concavity
in edge caps give, for each activation outcome,

    F_q(1_A,C) >= sum_k lambda_k F_q(1_A,C^k).

Apply the forest inequality and average. This argument avoids the false
requirement that each forest component respect the original fixed caps.

## Capped opposite-side supermodularity

For a fixed bipartite flow network, its value as a function of active
vertices is supermodular in one vertex on each side. For optimal flows
in the two one-added states, keep their common edgewise minimum. Orient
the remaining red-minus-blue flow left-to-right when positive and
right-to-left when negative. The right-side newly active vertex is a
pure source; the left-side newly active vertex has no incoming arcs.
Swap all flow on source-to-sink paths starting at the right vertex.
The outputs fit the both-added and neither-added states. Each edge's
new amount lies between the two old amounts, hence respects its cap;
endpoint loads stay between the corresponding old loads, and internal
loads are preserved. Total profit is unchanged. This establishes the
required four-state inequality. Independent checks were supplied by
the physical-rounding and heavy-forest agents.

## Double cover

Duplicate each vertex into left and right copies, and replace uv by
u_L v_R and v_L u_R, each with profit q_uv and cap C_uv. With duplicate
capacities, the flow optimum is exactly twice the original optimum:
duplicate an original feasible flow, or average the two oriented flows
of a double-cover solution. Apply the bipartite activation result, then
correlate each opposite-side twin pair using the preceding inequality.
This yields the candidate for general graphs as well.

## Checks and scope

The factor 12 in the cap premise is necessary for this particular
activation statement: on one edge with y=D_u=D_v=d and C=K d<1,
the expected recourse is K d(1/4+3d/4)^2. As d tends to zero, the
inequality requires K>=12.

The root's `five_hour_capped_activation_probe.py` completed 1,200 random
bipartite instances. K=12 and K=16 had no violations; the least observed
ratio for K=12 was about 1.0398. K=4 and K=8 did fail, as the single-edge
calculation predicts. These tests are nonexhaustive diagnostics only.

With categorical heavy matching support and bipartite combined support,
the capped recourse candidate gives a one-color law respecting actual
physical tiny-edge supplies. Inflating heavy weights and retaining 2 tau
slack permits per-pattern whole-edge rounding. The current consequence
is fractional coloring, not one finite integer palette with exact heavy
stocks and simultaneous coverage of every tiny edge. The latter remains
open; the unrestricted constants have not changed.
