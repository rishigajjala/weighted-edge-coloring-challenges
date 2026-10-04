# Two partial cases of the reciprocal-max policy

**Status (2026-10-03): limited analytic lemmas; they do not prove the uncapped two-sided local policy or the physical coloring bound.**

Let `e=uv` have target `y>0`, endpoint degree bounds `D_u,D_v<=1`, and activation probabilities `p_x=(1+3D_x)/4`. Suppose `v` has no competing tiny edges and the vertex activations are independent. First consider an **uncapped** probe coefficient:

`b= (4/3)y/(p_up_v) <= 12y`.

For every competitor `i` at `u` with target `a_i` and opposite-end activation probability `r_i`, take coefficient `b_i=min{(4/3)a_i/(p_u r_i),12a_i}`. Conditional on `u,v` active, its load at `u` is `T=b+sum_i b_i B_i`, where the independent `B_i` have means `r_i`. The probe flow is `b/max(1,T)`, so it suffices to prove `E[1/max(1,T)]>=9/16`.

Write `K=4/3`, `c=y(1/p_v−1)`. Since `D_v>=y`,

`c <= 3y(1−y)/(1+3y) <= 1/3`,

the last inequality being exactly `(3y−1)^2>=0`. Also `sum_i a_i<=D_u−y` and `b_i r_i<=K a_i/p_u`. Thus

`mu=E T <= K (D_u+c)/p_u <= K(1+c) <= 16/9`.

The middle inequality follows because `(D+c)/p(D)=4(D+c)/(1+3D)` is nondecreasing on `[0,1]` when `c<=1/3`. A second bound, using the fact that `(D−y)/p(D)` is increasing in `D`, is

`mu−b <= K (D_u−y)/p_u <= K(1−y) <= 4/3`.

Let `f(t)=1/max(1,t)`. If `b>=1`, `T>=1`, so Jensen and `mu<=16/9` give `E f(T)>=1/mu>=9/16`. For `0<=b<1`, the lower convex envelope of `f` on `[b,infinity)` is the line

`h_b(t)=1−(t−b)/t_0^2` for `b<=t<=t_0`,

followed by `1/t` for `t>=t_0`, where `t_0=1+sqrt(1−b)`. This is the line from `(b,1)` tangent to `1/t` at `t_0`; it lies below `f`. The envelope is decreasing, hence `E f(T)>=h_b(mu)` with the natural continuation after `t_0`.

If `b>=32/81`, then `t_0<=16/9`, so `mu<=16/9` gives `E f(T)>=h_b(16/9)=9/16`. If `b<=32/81`, then `t_0>=16/9` and `mu−b<=4/3`, so

`E f(T)>=1−(mu−b)/t_0^2 >=1−(4/3)/(16/9)^2 =37/64>9/16`.

Therefore `E z_e=p_up_v b E f(T)>=K y*(9/16)=3y/4`. The equality family `y=1/3`, `p_v=1/2`, with always-active competitors at `u` and `D_u=y+sum_i a_i`, sits in the `b>=1` Jensen case for small total competitors and has conditional load `16/9` exactly; for large total competitors `b` falls below one but the same conditional load remains `16/9`, so the proof's lower-envelope bound is nonsharp there.

## Cap-active probe: both endpoints may have competitors

Now suppose `b=12y<Ky/(p_up_v)`, equivalently `UV<16/9` where `U=1+3D_u`, `V=1+3D_v`, and `p_up_v=UV/16`. Allow competitors at **both** endpoints. Conditional on the probe endpoints active, write the two tentative loads as `T_u=b+C_u`, `T_v=b+C_v`, with nonnegative competitor loads. The probe guarantee is `E[1/max(1,T_u,T_v)]>=1/(UV)`.

The scalar tangent inequality `1/max(1,t)>=1−t/4` and `max(T_u,T_v)<=b+C_u+C_v` give

`E[1/max(1,T_u,T_v)] >= 1−[b+E C_u+E C_v]/4`.

The conditional means obey

`E C_u <=(16/3)(D_u−y)/U`, `E C_v <=(16/3)(D_v−y)/V`.

The tangent inequality holds for every `t>=0`: for `t<=1` it is immediate, and for `t>=1` the difference is `(t−2)^2/(4t)`. Thus it is enough to show

`12y+(16/3)[(D_u−y)/U+(D_v−y)/V] <=4(1−1/(UV))`.

The left side increases in `y`, since its derivative is `12−(16/3)(1/U+1/V)>=4/3`. Set `y=min(D_u,D_v)` and assume by symmetry `U<=V`.

Then the left side is `4(U−1)+16(V−U)/(9V)`. Multiplying the difference from the right side by the positive factor `9UV/4` gives

`P(U,V)=UV(14−9U)+4U^2−9`.

The cap-active condition and `U<=V` imply `U<=4/3`, so `14−9U>=2`. Hence `P` increases in `V`, and at `V=U` it equals `9[U^2(2−U)−1]>=0` for `U in [1,4/3]`. The required mean bound follows, and therefore

`E z_e=p_up_v 12y E[1/max(1,T_u,T_v)] >= (UV/16)12y/(UV)=3y/4`.

Combined with the first section, this establishes the one-star coordinate claim for all probes and the cap-active claim for arbitrary two-sided competitors. The uncapped two-sided case remains open for this explicit policy.
