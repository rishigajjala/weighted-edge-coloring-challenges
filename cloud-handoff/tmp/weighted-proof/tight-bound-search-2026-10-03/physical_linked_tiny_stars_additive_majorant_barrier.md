# An exact barrier to additive many-sums majorants for star overload

**Status: proved obstruction to one proof route, not to integer colouring.** The Harris--Srinivasan many-sums proposition in the manuscript controls sums of nonnegative contributions from independent choices. It cannot be applied to the empirical-permutation overload of `physical_linked_tiny_stars_empirical_transport.md` by replacing one star's overload with a separable additive majorant, one term per independently permuted source, while retaining the required half-deficit mean. The loss can exceed the entire half budget in a literal physical heavy-matching/tiny-star example.

## Three cyclic source lists

Let `N=3m`. At one fixed-capacity tiny-star hub put three leaves. Each leaf source list has `N` rows, with proposed tiny load one in exactly one block of `m` consecutive rows and load zero elsewhere. Restrict its permissible row permutations to the three cyclic shifts by `0,m,2m`; write its choice `s_i∈{0,1,2}`. The three source choices are independent and uniform. In each normal row the hub capacity is one, so total hub overload is

`C(s_1,s_2,s_3)=Σ_(j=1)^N (Z_1(j)+Z_2(j)+Z_3(j)−1)_+`.

For a fixed row, each `Z_i(j)` is independent Bernoulli-`1/3`. Hence

`E C/N=P(Bin(3,1/3)=2)+2P(Bin(3,1/3)=3)=8/27`.

When all three shifts are the same, all three high blocks coincide. In their `m` rows the load is three, so

`C(s,s,s)=2m=2N/3` for each `s=0,1,2`.

Now suppose arbitrary real functions `f_i:{0,1,2}→R` give a **pointwise separable upper bound**

`C(s_1,s_2,s_3)≤f_1(s_1)+f_2(s_2)+f_3(s_3)` for all choices.

Apply it to the three diagonal choices and sum. This yields

`Σ_i Σ_(s=0)^2 f_i(s)≥3·(2N/3)=2N`.

Under the independent uniform source choices, the additive upper bound therefore has expectation at least

`E[Σ_i f_i(s_i)]≥2N/3>N/2`.                   (1)

This holds even if the `f_i` may be negative. The true expected overload is only `8N/27`. The obstruction is the source interaction in `(Σ Z_i−1)_+`: a source's charge cannot be fixed independently of the other two permutations without paying for the fully aligned outcome in every diagonal shift.

## Literal physical realization

Take `τ=1/k` with integer `k≥3`. For each of the three tiny leaves, use `km` physical tiny edges of weight `τ` on its spoke, packed in the leaf's `m` no-heavy bins in groups of `k`; each such bin has tiny load one. Join that leaf to a distinct outside vertex by `2m` physical unit-heavy edges. These `2m` heavy identities occupy the other leaf bins and the corresponding outside-vertex bins. The heavy simple support is a matching, the tiny simple support is one star, and the combined support is a tree (hence bipartite). At the hub, pack one leaf's `km` tiny edges per block of `m` bins, so its total `3m=N` local bins are feasible. The three full heavy-pair source lists therefore have exactly the stated load profiles; cyclically shifting their `N` rows preserves every physical heavy and tiny edge exactly once.

The one-star sorting theorem deliberately anti-aligns these lists and gives zero overload. Thus (1) is **not** an instance obstructing simultaneous good permutations. It rules out the direct route of expressing the hinge overload as an additive independent-source sum with expected value at most `N/2` and then applying the many-sums proposition. A full linked-star integer proof must retain the interaction among source permutations, use a nonseparable resampling theorem, or exploit additional structure.
