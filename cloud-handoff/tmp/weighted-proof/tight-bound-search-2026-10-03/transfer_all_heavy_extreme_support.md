# Sparse extreme support for arbitrary heavy packets plus fluid

**Status: proved structural reduction.** This applies to the mixed
model in which every discrete type has weight strictly above `1/2`
and all other edges are divisible fluid. Heavy support, fluid support,
parallel types, and edge profits are arbitrary. It does not prove
the desired unrestricted `3/2` inclusion.

## Exact local polytope

Write `x_e` for the expected count of heavy type `e` in one pattern
and `y_f` for the expected amount of fluid edge `f`. At each vertex
`v`, the complete local configuration hull is described by exactly
two families of inequalities:

`H_v(x)=sum_{e heavy at v} x_e <=1`,
`L_v(x,y)=sum_{e heavy at v}w_e x_e+sum_{f fluid at v}y_f<=1`,
`x,y>=0`.                                               (1)

Necessity is immediate: one feasible local pattern has at most one
heavy item and total weighted load at most one. For sufficiency,
choose heavy state `e` with probability `x_e` and no heavy state
with the remaining probability. In state `e` the available fluid
capacity is `1-w_e`, and in the empty state it is one. Its mean is
`r=1-sum w_e x_e`. If `r>0`, allocate every fluid edge `f` amount
`(y_f/r)` times the realized capacity; the total fits because
`sum_f y_f<=r`. If `r=0`, (1) forces every `y_f=0`.
This constructs the full local law. Different vertex laws need only
agree in their type/fluid means to define a point of the local hull.

## Every basic positive support is 4-degenerate

Choose an extreme optimum of the finite local LP (1) for any
nonnegative profit vector. Let `E_+` be its positive heavy-type and
fluid-edge coordinates, counting parallel types separately. For
every vertex subset `S`,

`|E_+[S]| <= 2|S|`.                                   (2)

Indeed, columns for edges with both endpoints in `S` have nonzero
entries only in the two rows `H_v,L_v` with `v in S`. At an extreme
point, positive columns are linearly independent after restriction
to active constraint rows: any dependence permits a sufficiently
small perturbation in both signs without violating nonnegativity or
slack rows. Their subfamily on `S` is therefore independent in a
space of dimension at most `2|S|`, proving (2). Every induced
positive-support subgraph has average degree at most four, so it
has a vertex incident with at most four positive **types**. Thus
the positive multitype support is 4-degenerate.

If the combined heavy-plus-fluid support is bipartite, the sharper
bound is

`|E_+[S]| <= 2|S|-2` for `|S|>=2`.                    (3)

Choose signs `+1,-1` on its bipartition. The signed sum of the
heavy-count rows vanishes on every internal heavy column and on
every fluid column; independently, the signed sum of the load rows
vanishes on every internal column because each edge has the same
weight/flow coefficient at both endpoints. These are two
independent left-kernel vectors of the restricted `2|S|`-row
matrix. Equation (3) follows, so every induced positive support
has average degree strictly below four and some vertex incident
with at most three positive types: it is 3-degenerate.

These are **type-degree** statements. A support bundle may have
multiple positive heavy or fluid types, each consuming one column.
The reduction is valid for a profit optimum because a finite LP
always has an extreme optimum.

## The general count `2|S|` can be attained

On five vertices, take five heavy edges forming one `C_5`, each of
weight `w in (1/2,1)`, and take five fluid edges forming its
complementary `C_5`. Put `x_e=1/2` on every heavy edge and
`y_f=(1-w)/2` on every fluid edge. At each vertex its two heavy
counts sum to one, and the weighted heavy load `w` plus fluid load
`1-w` equals one. Thus all ten local rows are tight and all ten
variables positive.

The heavy-count submatrix is the unsigned incidence matrix of an
odd cycle, hence invertible. After its columns are eliminated, the
fluid-load submatrix is the unsigned incidence matrix of the other
odd cycle, also invertible. The full ten-by-ten tight matrix is
therefore invertible, so this point is extreme and has exactly
`2|V|=10` positive types. The 4-degeneracy bound cannot be lowered
merely by counting local LP rows.

## Consequence and limit

An arbitrary-heavy-plus-fluid `3/2` proof may choose a local optimum
whose active support can be peeled one vertex of type degree at most
four, or at most three in the bipartite case. This connects the
unrestricted target to a bounded-interface insertion problem.
However, a theorem only for isolated graphs on five vertices does
not perform the insertion: the already rounded remainder imposes a
joint boundary law on the neighboring vertices. A valid induction
must preserve or repair that law while adding the peeled vertex.
