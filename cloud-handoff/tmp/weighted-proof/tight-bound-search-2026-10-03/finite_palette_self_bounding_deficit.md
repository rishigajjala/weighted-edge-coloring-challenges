# Finite-palette deficit as a self-bounding function (2026-10-03)

This is a structural observation, **not** a graph-order-uniform rounding theorem.

Let color blocks `c=1,...,M` be independent. In block `c`, the chosen heavy state and a feasible tiny flow assign nonnegative `z_{e,c}` to each physical tiny edge. The per-color endpoint constraint gives `sum_{e at v} z_{e,c} <= 1`. Write `S_e=sum_c z_{e,c}` and let the physical stock be `w_e`. Define the vertex deficit

`U_v = sum_{e at v} (w_e-S_e)_+`

and covered stock `C_v=T_v-U_v=sum_{e at v} min(w_e,S_e)`, where `T_v=sum_{e at v}w_e`.

Delete one color block `c` and call the resulting deficit `U_v^{(c)}`. Then

`0 <= U_v^{(c)}-U_v <= sum_{e at v}z_{e,c} <= 1`.

Moreover, **the sum of deletion influences obeys a self-bounding inequality**:

`sum_c (U_v^{(c)}-U_v) <= C_v = T_v-U_v`.

Proof is edgewise. If `S_e<=w_e`, deletion of block `c` increases deficit by `z_{e,c}`, so the sum is `S_e=min(w_e,S_e)`. If `S_e>w_e`, put `t=S_e-w_e`. The increment is `(z_{e,c}-t)_+`; if `A={c:z_{e,c}>t}` is nonempty, its sum is `sum_{c in A}z_{e,c}-|A|t <= S_e-t=w_e=min(w_e,S_e)`. It is zero if `A` is empty. Sum over incident edges.

Thus `C_v` is monotone, has deletion influence in `[0,1]`, and is self-bounding in the standard sense. Standard concentration gives an individual vertex deficit tail depending on `T_v` and the expected covered stock, without a degree factor. If every physical edge has relative cap `z_{e,c}<=K w_e/N` and expected total load `(1+eta)w_e`, ordinary bounded-summand Chernoff gives `E(w_e-S_e)_+ <= w_e exp(-Omega_{eta,K}(N))`; summing at `v` gives `EU_v <= T_v exp(-Omega(N))`. This is compatible with graph-order-independent **single-vertex** control.

The open quantifier is simultaneous control of every vertex. A union bound still costs `log |V|`. In the independent-block formulation each block can influence vertices throughout the graph, so the ordinary variable-dependency Lovasz local lemma has no bounded dependency degree. A dimension-free simultaneous selection or suitable local resampling theorem is still needed. The self-bounding identity is potentially an input to such a theorem; it does not supply one by itself.

For the K=3 two-star expected-max shortcut at `y->0,D_u=D_v=1`, exact rational values are `253/192` for three equal spokes against three, `698159/524288` for three against four (gap `2675/1572864` below `4/3`), and `5639452987/4294967296` for four against four. The very small three-versus-four margin makes a variance-only proof implausible; indeed iid `Uniform[0,2]` satisfies mean 1 and variance 1/3 but has `E max(1/3,X,Y)=4/3+1/324`.
