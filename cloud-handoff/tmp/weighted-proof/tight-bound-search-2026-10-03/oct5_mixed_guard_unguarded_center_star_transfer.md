# Mixed-weight guarded leaves: capped transfer at an unguarded star center

5 October 2026. **Scoped exact theorem.** This extends the unguarded-center branch case to arbitrary categorical heavy weights `w_h∈[0,1]` and arbitrary fluid star degree. It does not handle a center incident to a heavy guard, arbitrary fluid branching, or physical integer colors.

Let the positive fluid support be a star or a vertex-disjoint star forest. Every star center is unguarded. The simple support of heavy guards is a matching; at each guard pair, categorical heavy identities `h` have original marginals `x_h`, total presence at most one, and weight `w_h∈[0,1]`. Their endpoint residual allowance is `D_P=1−Σ_h w_h x_h`. A fluid identity `e` has target `y_e≥0`, conditional cap `C_e≥12y_e`, and the local target loads obey `Σ_{e∋v}y_e≤D_v`. Then one fixed law, selecting guard states independently across pairs with `P(h)=2x_h/3`, admits a conditional feasible capped fluid policy with every fluid identity's mean exactly `2y_e/3`. The same law works across all vertex-disjoint stars even if a guard pair links leaves in different stars.

## One unit-profit prefix

Fix one star and a prefix of its fluid identities. Put `s=Σ_prefix y_e≤1`. Group its leaves by heavy pair; each group has one or two leaves, and a singleton unguarded leaf is treated as a deterministic residual-one group. Write `Y_i` for a group's prefix target mass. Every guarded endpoint in group `i` has allowance at least its own prefix load; because there are at most two endpoints, their common pair allowance satisfies `D_i≥Y_i/2`. Under the scaled independent categorical law, their common actual residual `R_i` has

`E R_i=1−(2/3)(1−D_i)≥(1+Y_i)/3=:p_i`.

Let `C_{iℓ}` be the sum of prefix caps at leaf `ℓ` of group `i`. In a sampled heavy state the maximum amount the group could send to a free center is `Σ_{ℓ∈i}min(R_i,C_{iℓ})`. Truncate it at one and call the result `B_i∈[0,1]`. For `0≤r≤1`, `min(r,C)≥r min(1,C)`, and `Σ_ℓ min(1,C_{iℓ})≥min(1,Σ_ℓ C_{iℓ})`. Since `Σ_ℓ C_{iℓ}≥12Y_i`, this proves **pointwise**

`B_i≥c_i R_i`, where `c_i=min(1,12Y_i)`.

The star center has capacity one. Its optimum prefix throughput is `min(1,Σ_i B_i)`. For numbers `B_i∈[0,1]`,

`min(1,Σ_i B_i)≥1−∏_i(1−B_i)`.

Different guarded groups are independent under the chosen heavy law, so the expected prefix throughput is at least `1−P`, where

`P=∏_i(1−c_i p_i)`.

We prove `P≤1−2s/3`. A **weak** group has `Y_i<1/12`; then `c_i=12Y_i` and its factor is at most `exp(−4Y_i)`. A **strong** group has `Y_i≥1/12`; then `c_i=1` and its factor is at most `(2−Y_i)/3`.

If all groups are weak, `P≤exp(−4s)≤1−2s/3` for `0≤s≤1`. For the last inequality, `1−exp(−4s)−2s/3` is concave, zero at `s=0`, and positive at `s=1`, so it lies above its endpoint chord.

Otherwise let `S` be total strong-group mass and `W=s−S` weak mass. Merging two strong factors does not decrease their product upper bound: for `a+b≤1`,

`[(2−a)(2−b)]/9≤(2−a−b)/3`.

Thus `P≤[(2−S)/3] exp(−4W)`. Define

`G(W)=3−2S−2W−(2−S)exp(−4W)` on `0≤W≤1−S`.

It is concave. Its endpoints are `G(0)=1−S≥0` and `G(1−S)=1−(2−S)exp(−4(1−S))≥0`, since `1+t≤exp(4t)` for `t=1−S`. Hence `G(W)≥0` throughout, exactly the required `P≤1−2s/3`.

## Profits and exact marginals

For a fixed state of a fluid star, filling identities in descending profit order maximizes every prefix throughput simultaneously. The unit-prefix bound therefore integrates by the usual layer-cake identity to `E F_q(R,C)≥(2/3)Σ_e q_e y_e` for every nonnegative profit vector `q`. Recourse adds across vertex-disjoint stars; the fact that a heavy pair may link leaves of two stars does not affect this expected sum. The feasible expected-fluid region is compact, convex, and downward closed. Support-function separation supplies a conditional fluid policy with exact coordinate means `2y_e/3`, while all categorical heavy identities already have exact means `2x_h/3`.

The proof uses only the first moment of each real residual and the independence of *different* heavy pairs. In particular it does not require `w_h>1/2`. The guarded-center star remains open: independent pair selection can fail there already for unit guards, and a common occupancy mode changes the joint real-residual profile in ways not captured by this product argument.

**Cap constant.** The same proof actually works with the cleaner hypothesis `C_e≥4y_e`. Replace `c_i` by `min(1,4Y_i)`. A weak factor is then at most `exp(−4Y_i/3)`. For all weak groups, `exp(−4s/3)≤1−2s/3` on `[0,1]`: the difference of the right and left sides is concave, zero at zero, and positive at one. In the strong-plus-weak case, the bound becomes `[(2−S)/3]exp(−4W/3)`; its desired comparison with `1−2(S+W)/3` is concave in `W`, nonnegative at `W=0`, and at `W=1−S` follows from `(1+t)exp(−4t/3)≤1` for `t=1−S`. Strong-factor merging is unchanged. More generally this argument works for cap multiplier `K≥3 ln 3`; the value four avoids a logarithmic premise. No claim of sharpness for this method or theorem is made.
