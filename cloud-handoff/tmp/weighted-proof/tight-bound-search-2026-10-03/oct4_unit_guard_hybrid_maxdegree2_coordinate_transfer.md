# Unit-heavy hybrid: direct capped transfer when the fluid target has degree at most two

4 October 2026. This is a scoped divisible one-color theorem, not an
integer weighted-edge-coloring improvement. Unlike the star proof in
`unit_guard_capped_star_hybrid_two_thirds_audited.md`, the fluid support
may contain paths or odd cycles and the conclusion preserves every fluid
coordinate by one explicit profit-independent policy. It does not cover
arbitrary branch vertices.

## Statement

Let all heavy edges have weight one and let their simple support be a
matching. A pair may have several parallel physical heavy identities;
their categorical local probabilities sum to `x_P≤1`. At an unguarded
vertex put `x_P=0`. Let `D_v=1−x_{P(v)}`. Let nonnegative divisible-fluid
target `y` obey `Σ_{e∋v} y_e≤D_v` at every vertex and let its positive
physical-edge support have degree at most two (parallel coordinates count
separately). Suppose every fluid edge has conditional cap `C_e≥4y_e`.
There is a one-color distribution with each physical heavy identity
present with probability `(2/3)x_h` and each fluid coordinate having
mean `(2/3)y_e`. No bipartiteness is required.

In fact the conclusion holds with arbitrary fluid degree whenever the
local condition in the final section holds at every vertex.

## Fixed heavy law and edgewise fluid rule

Use the same globally mixed heavy law as the capped star theorem:
with probability `3/4`, sample pair states independently at marginal
`(2/3)x`; with probability `1/4`, use a common uniform threshold to
make pair `P` free with probability

`p_P=1−(2/3)x_P=(1+2D_P)/3`,

and choose an occupied identity conditionally according to its original
categorical frequencies. Both modes individually give the requested
heavy identity marginals. An unguarded vertex is always free.

For a fluid edge `e=uv`, let `P_e` be the probability that both endpoint
heavy sources are free under this fixed law. If the endpoints belong to
distinct sources with free probabilities `p_u,p_v`, then

`P_e=(3/4)p_u p_v+(1/4)min(p_u,p_v)`.

If they belong to the same heavy pair, `P_e=p_u=p_v`; unguarded endpoints
are interpreted as probability one. Define the conditional fluid rule

`f_e = [(2/3)y_e/P_e] 1{both endpoint sources free}`.

It has exact mean `(2/3)y_e`. Since every source free probability is at
least `1/3`, the distinct-source formula gives `P_e≥1/6`; the same-source
case gives `P_e≥1/3`. Hence `f_e≤4y_e≤C_e` in every state.

## Vertex capacity

Fix a vertex `v` and an incident positive-target edge `e`. Put
`p(t)=(1+2t)/3`. Local feasibility gives `y_e≤D_v` and
`y_e≤D_u` at its other endpoint. Thus `p_v≥p(y_e)` and
`p_u≥p(y_e)`. The distinct-source formula, split according to which
probability is smaller, yields

`P_e≥p(y_e)[(3/4)p_v+1/4]
    = (1+2y_e)(1+D_v)/6`.

For a same-source edge, `P_e=p_v` also exceeds this expression:
`p(y_e)≤p_v` and `(3/4)p_v+1/4≤1`. An unguarded endpoint only
increases the probability. Consequently, in every heavy state,

`Σ_{e∋v} f_e ≤ [4/(1+D_v)] Σ_{e∋v} y_e/(1+2y_e)`.

The function `g(t)=t/(1+2t)` is increasing and concave on `[0,1]`.
With at most two positive incident coordinates, pad with a zero if
necessary and write `S_v=Σ_{e∋v}y_e≤D_v`. Jensen gives

`Σ_{e∋v}g(y_e)≤2g(S_v/2)=S_v/(1+S_v)
                   ≤D_v/(1+D_v)`.

Therefore the state's incident fluid load is at most

`4D_v/(1+D_v)^2≤1`,

the last inequality being `(1−D_v)^2≥0`. Heavy edges are present only
when their endpoints' fluid variables are all zero under this rule, so
the complete one-color pattern is feasible. This proves the coordinate
marginals directly, without a support-function or profit argument.

## More general local sufficient condition

If `v` has `k_v≥1` positive incident fluid coordinates, the same Jensen
calculation gives

`Σ_{e∋v} f_e ≤ 4D_v/[(1+D_v)(1+2D_v/k_v)]`.

Thus the policy works whenever this expression is at most one at every
vertex. It is automatic for `k_v≤2`. For `k_v=3` it holds whenever
`D_v≤1/2`; for large degree the threshold tends to `D_v≤1/3`.
The remaining difficulty for this direct policy is precisely a vertex
with both high residual allowance and at least three positive target
edges. The existing capped star theorem handles any one such star via
adaptive optimal recourse, but the above calculation alone does not
handle overlapping branch vertices.
