# Exact failure of independent 2/3 paired activation

This refutes the proposed independent activation inequality for general
fluid graphs. It does **not** establish a weighted-edge-coloring lower
bound: a different correlated activation law or a direct coloring may
still succeed.

Take a two-leaf star with center `c` and leaves `u,v`. Group `u,v` into
one activation block `P`; make `c` a singleton block `Q` (or pair it
with an isolated unused vertex). Both edges have unit profit. Put

    y_uc=y_vc=t,       D_P=t,       D_Q=2t,

where `1/4<t<1/2`. This is a feasible fractional fluid target because
the two leaves have degrees `t` and the center has degree `2t<=1`.
Its target value is `2t`.

Activate blocks independently with the proposed probabilities

    p_P=(1+2t)/3,       p_Q=(1+4t)/3.

The active star has fractional (and integral) matching value one if
both blocks activate and zero otherwise. Consequently

    E F_q(1_A) = p_P*p_Q = (1+6t+8t^2)/9,
    (2/3) q·y = 4t/3 = 12t/9,
    E F_q(1_A) - (2/3)q·y
      = (1-2t)(1-4t)/9 < 0.

For example, `t=3/8` gives `p_P=7/12`, `p_Q=5/6`, so the expected
recourse value is `35/72` while the required value is `36/72`.

The failure is the combination of two same-block substitute leaves
and a center whose fluid degree is below one. The previously observed
equality case at `t=1/2`, `D_Q=1` sits at the endpoint of this open
failure interval. A proof using independent paired activation at
factor `2/3` must compensate this star elsewhere, change probabilities,
or use correlations between blocks.

More generally, for a proposed recovery factor `alpha` and the natural
independent block activation law `p_P=1-alpha+alpha*D_P`, the same star
has difference

    p_P*p_Q - alpha*(2t)
      = (1-alpha)^2 + alpha*(1-3*alpha)*t + 2*alpha^2*t^2.

For `alpha>1/3`, its unconstrained minimum occurs at
`t=(3*alpha-1)/(4*alpha)`, which lies in `(0,1/2)` for `alpha<1`, and
equals `(7-10*alpha-alpha^2)/8`. Thus this independent activation
scheme cannot certify a factor better than

    1/(4*sqrt(2)-5) = (4*sqrt(2)+5)/7 = 1.5224077... .

This is only a limitation of that **independent activation scheme**;
correlating activation of `P` and `Q` can make the two-leaf star's
recourse value larger.

For clarity, even adding a unit-heavy physical edge across the two
leaves (profit `a`) and another unit-heavy edge at the center to a
private vertex (profit `b`) does not turn this particular star into a
larger-than-`3/2` lower bound. If the symmetric spoke total is `s`,
the optimal local heavy means are `x_P=1-s/2` and `x_Q=1-s`, giving

    L = a+b+s*(1-a/2-b),   0<=s<=1.

Hence the local optimum is `max(a+b,1+a/2)`. The global one-color
optimum is `max(a+b,1)`: the two heavy edges fit together, whereas
either blocks all fluid. Consequently

    max(a+b,1+a/2) / max(a+b,1) <= 3/2,

with equality only in the ordinary one-heavy-edge triangle limit
`a=1,b=0`. The activation-law counterexample therefore identifies a
proof-method obstruction, not a new gap instance.

There is also a simple obstruction to chaining these *tight* star
defects. A relation with leaf-block degree `t` and center-block degree
`2t` uses both ports of its leaf block and one port of its center
block. If that center block also serves as the two-leaf block of a
second relation of size `t`, its shared port degree is at least `3t`.
For `t>1/3` this is infeasible. For `1/4<t<=1/3`, the raised center
activation probability `p(3t)=(1+6t)/3` makes the first relation's
independent intersection satisfy its target:

    p(t)*p(3t) - (4/3)t
      = (1-4t+12t^2)/9 > 0.

The second relation's leaf block then also has the larger probability,
so its analogous product is safe. This does not rule out more elaborate
interacting stars, but a direct same-size chain no longer carries the
local independent-activation defect.
