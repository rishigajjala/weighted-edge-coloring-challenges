# Mixed-guard hybrid audit and unguarded-center star transfer

5 October 2026. Scratch result. The exact parametric failure below is
outside the heavy-weight `w>1/2` regime. The positive theorem covers
unguarded-centered, vertex-disjoint fluid stars with arbitrary
categorical guard weights in `[0,1]`; it does not cover guarded centers
or arbitrary branching.

## Audit of `oct5_mixed_guard_hybrid_lp_probe.py`

For pair `i`, write `x_i=Σ_h x_{ih}`. The `states()` enumerator uses
probability `1−alpha x_i` for no selected guard and `alpha x_{ih}`
for selected type `h` in independent mode. In common mode it uses one
uniform threshold `U`: pair `i` is occupied iff `U<=alpha x_i`, and
conditional type probability is `x_{ih}/x_i`, independently across
pairs. For an enumerated joint state, its common-mode interval length
is exactly

`max(0, min_{occupied i}(alpha x_i) − max_{unoccupied i}(alpha x_i))`,

with the empty minimum one and empty maximum zero. Multiplying by
conditional type probabilities and mixing with weights `3/4,1/4`
matches the stated fixed law. Its per-pair residual is `1−w_h` if
occupied and one if free, shared by the pair's two endpoints.

The `retention()` LP uses variables `prob(state)*flow_e(state)`, bounds
each by `prob(state)*min(1,12y_e)`, enforces every state's vertex
capacity `prob(state)*R_v`, and requires each expected fluid coordinate
to be at least `r y_e`. It maximizes `r`. The effective cap
`min(1,12y_e)` is valid because no one fluid edge can exceed either
unit vertex capacity; it tests the hardest permitted choice `C=12y`.
The artificial upper bound `r<=2` cannot mask a failure below `2/3`.
Floating solver tolerances and omission of states below `1e−13` mean
the random run is diagnostic, not a certificate. Its sampled guard
weights are all above `1/2`; its 4,000 no-failure cases do not cover
weights below `1/2`, and do not prove the heavy-weight theorem.

## Exact low-weight failure of the fixed hybrid law

Take four vertices. Leaves `0,1` form one unit-guard pair with guard
target `x_L=1−m`. Center `2` and an otherwise isolated partner `3`
form one guard pair with target one and guard weight `w_C=1−2m`.
Put one unit-profit fluid edge from each leaf to the center, with
target `m` and cap at least `12m`. For `m∈(1/3,1/2)`, all targets are
locally feasible: leaves have allowance `m`, center has allowance
`2m`, and each leaf/center row is tight. The center guard weight lies
in `(0,1/3)`, so this is not a counterexample for `w>1/2`.

At `alpha=2/3`, the leaf pair is free with marginal
`p_L=(1+2m)/3`; the center guard is occupied with marginal `2/3`,
giving center residual `2m` when occupied and one when absent. Since
`12m>1`, conditional optimal fluid throughput is the center residual
when the leaf pair is free, and zero otherwise. Independent mode has
expected throughput

`I = p_L*(1/3+4m/3) = (1+6m+8m^2)/9`.

In common mode, the leaf pair is blocked for `U<=2(1−m)/3`.
For `2(1−m)/3<U<=2/3`, the leaves are free and the center residual
is `2m`; for `U>2/3`, the center residual is one. Therefore

`C = (2m/3)*(2m)+1/3 = 1/3+4m^2/3`.

The hybrid expected maximum is

`(3/4)I+(1/4)C = 1/6+m/2+m^2`.

The desired fluid target has total mean `alpha*(2m)=4m/3`.
The deficit is exactly

`4m/3 − (1/6+m/2+m^2) = (3m−1)(1−2m)/6 >0`.

At `m=2/5`, the expected maximum is `79/150`, the desired amount is
`80/150`, and the best uniform coordinate retention is exactly
`79/120<2/3`. Exactness of the retention ratio follows by symmetry:
split every available center capacity equally between the two spokes.
Directly calling the script's `states()` and `retention()` on this
four-vertex instance returned the four state probabilities
`(7/30,11/30,1/10,3/10)`, expected throughput `79/150`, and retention
`79/120`, agreeing with the formulas.

## Mixed categorical guards on unguarded-centered stars

**Theorem.** Let the simple support of categorical guard sources be
disjoint pairs. At pair `i`, guard identity `h` has target `x_{ih}>=0`
and weight `w_{ih}∈[0,1]`, with `Σ_h x_{ih}<=1`; its mean weighted
occupancy is `a_i=Σ_h w_{ih}x_{ih}` and both endpoints' allowance is
`D_i=1−a_i`. Unguarded vertices have allowance one. Let the fluid
support be one star with an **unguarded center**, or a vertex-disjoint
forest of such stars; parallel fluid identities are allowed. Let
`y>=0` obey every local allowance and `C_e>=12y_e`. There is a single
law of categorical guards and feasible capped fluid flows with means
`(2/3)x_{ih}` and `(2/3)y_e` for every coordinate. Guard pairs may
link leaves of different stars.

**Proof.** Independently across guard pairs, choose identity `h` with
probability `alpha x_{ih}`, or no identity with the remaining
probability, where `alpha=2/3`. This law is fixed independently of
fluid profits. Let `R_i` be the pair's realized residual capacity,
shared by its endpoints. Its mean is

`p_i=E R_i=1−alpha a_i=(1+2D_i)/3`.

Fix one star and a nonnegative profit vector `q`. For a realized real
residual vector `R`, let `F_q(R,C)` be its capped optimal fluid value.
This is jointly concave in all leaf capacities: a convex combination
of feasible flows for two capacity vectors is feasible for the
combined vector. Repeating the same pair capacity at two leaves is an
affine restriction, so the concavity remains valid in pair coordinates.
Conditional on `R`, independently for every guard pair draw one
Bernoulli bit `B_i` of mean `R_i`, shared by its two endpoints.
Conditional Jensen gives

`F_q(R,C) >= E[F_q(B,C) | R]`.

The guard pairs were independent and the conditional bits are
independent across pairs. Hence the unconditional `B_i` are
independent Bernoulli bits with free probabilities `p_i`. This is
exactly the independent mode of the audited **unit-guard** capped-star
theorem applied to effective unit-guard targets `a_i`: these lie in
`[0,1]`, and the fluid target respects `D_i=1−a_i`.

To use that audited theorem without assuming its common mode is
available, compare the two binary laws on an unguarded-centered star.
For a profit prefix `P`, group leaves by guard pair and let `b_i(P)`
be the total prefix flow available through group `i` when active,
respecting each leaf's unit capacity and its incident edge caps.
The maximum prefix throughput is

`T_P(B)=min(1, Σ_i b_i(P) B_i + b_0(P))`,

where `b_0(P)` accounts for deterministic unguarded leaves. This is
a submodular function of the pair-bit set. Greedy filling in decreasing
profit order maximizes every prefix throughput simultaneously, so
`F_q(B,C)` is a nonnegative layer-cake sum of these submodular prefix
functions and is itself submodular.

Among Bernoulli laws with fixed marginals `p_i`, the common-threshold
comonotone law minimizes the expectation of a submodular set function.
One proof repeatedly moves equal probability mass from incomparable
sets `A,B` to `A∩B,A∪B`; submodularity says this cannot raise the
expectation, while all one-coordinate marginals remain fixed. A
terminal chain-supported law is the common-threshold law. Therefore
the independent-mode star value `I_q` is at least the common-mode
value `C_q`.

The audited unit-guard capped-star theorem states
`(3/4)I_q+(1/4)C_q >= alpha q·y`. Hence

`E_real F_q(R,C) >= I_q >= alpha q·y`.

For a vertex-disjoint star forest, statewise fluid recourse values
add. Shared guard pairs across different stars do not change the
expectation of this sum. Thus the support inequality holds for every
nonnegative `q` under the same guard law. The set of attainable mean
fluid vectors under this law is compact, convex, and downward closed;
support-function separation yields a conditional feasible flow policy
whose means dominate `alpha y`, and downward thinning gives exact
means `alpha y`. This proves the theorem.

The unguarded-center condition is essential to this comparison:
when the center is guarded, center/leaf availability is complementary
for flow value, and the set function over pair bits need not be
submodular. The low-weight example above shows that the specified
hybrid fixed law can fail at a guarded center.
