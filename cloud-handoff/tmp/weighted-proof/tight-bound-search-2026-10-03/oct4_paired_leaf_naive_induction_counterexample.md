# A one-leaf recourse induction step fails inside a proved unit-guard star

4 October 2026. This is an obstruction to a **proof step**, not to the
fixed-hybrid two-thirds inclusion. The full star instance below has ample
surplus and lies within the audited capped star theorem.

Let leaves `u,z` share a unit-heavy pair of local presence `x=9/10`,
so their original residual allowance is `D=1/10`. Let center `w` be
unguarded. Fluid edges `wu,wz` each have target `y=1/10` and cap at
least `12y=6/5`. Give them profits `q_wu=1`, `q_wz=2`. The local
target is feasible: each leaf has heavy load `9/10` plus fluid load
`1/10`, and `w` has fluid load `1/5`.

Under the fixed `3/4` independent-scaled plus `1/4` comonotone-scaled
unit-heavy law, the leaf pair is free with probability
`p=(1+2D)/3=2/5` in each mode. When it is free, the optimal fluid
recourse routes one unit on `wz` for profit two. Thus full expected
recourse equals `4/5`.

Try the usual forest-leaf induction step: delete `wu` of target mass
`a=1/10`, and reduce the neighbor `w`'s allowance from one to
`1−a=9/10`. This reduced instance can be realized physically by
adding a separate unit-heavy guard at `w` of local presence `1/10`.
Its scaled free probability is `p'=(1+2(9/10))/3=14/15`.
The remaining target on `wz` is still locally feasible.

In the independent mode, reduced recourse expectation is
`2(14/15)(2/5)=56/75`. In the comonotone mode, the smaller leaf
threshold `2/5` forces `w` free whenever `z` is free, so its expected
recourse is `2(2/5)=4/5`. The full hybrid reduced recourse equals

`(3/4)(56/75)+(1/4)(4/5)=19/25`.

Consequently the full-minus-reduced recourse gain is only
`4/5−19/25=1/25`, less than the deleted target profit
`(2/3)a q_wu=1/15`. The inductive inequality

`E F(full)−E F(reduced) >= (2/3)a q_leaf`

is false, even on a two-edge star with caps above `12y`. There is no
contradiction to the theorem: the reduced expected recourse `19/25`
is far larger than its own scaled target `(2/3)(1/10)·2=2/15`.
An extension to arbitrary fluid forests must carry quantitative surplus
or remove paired-source groups together; bare per-leaf recourse
differences cannot close the induction.
