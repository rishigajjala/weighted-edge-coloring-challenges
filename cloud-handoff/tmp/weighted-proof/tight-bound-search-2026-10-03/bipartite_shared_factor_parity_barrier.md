# A 4/3 equal-count barrier for arbitrarily frustrated shared 2-factors

**Status.** Rigorous barrier to the all-edges-equal counting lower
certificate, not a coloring upper bound and not an exclusion of unequal
price certificates.

Let `H` and `M` be two 2-regular spanning factors on the same even-order
vertex set `V`, each with `n=|V|` distinct edge types. Assume each factor
is bipartite (as it is when their union is bipartite). Give every `H` type
weight above `1/2` and every `M` type weight in `(1/3,1/2]`. Replace each
type by `N` physical copies. At every vertex, assume its two `H` and two
`M` types admit a perfect compatible pairing, so all `4N` incident
physical edges fit in `2N` bins. The heavy edges alone force `2N` bins,
so `bp(G_N)=2N`.

**Claim.** Some feasible color contains at least `3n/4` physical edges,
independently of factor size, cycle structure, weights, and local pairing
frustration. Hence the equal-profit count certificate
`2nN/(max edges per color)`, divided by `bp=2N`, is at most `4/3`.

**Proof.** Choose independently and uniformly one of the two alternating
perfect matchings on every cycle of `H`, and likewise on every cycle of
`M`. Their union contains exactly `n/2+n/2=n` edges and presents one
heavy and one medium edge at each vertex. At one vertex write the heavy
weights `h_1≤h_2` and medium weights `m_1≤m_2`. Perfect compatible
pairability implies `h_1+m_2≤1` and `h_2+m_1≤1`; also
`h_1+m_1≤1`. Only the fourth pair `(h_2,m_2)` can be incompatible.
Each factor's random matching selects either incident edge with
probability `1/2`, and the two factors are independent. Thus the
probability that the chosen pair is incompatible at this vertex is at
most `1/4`. The expected number of bad vertices is at most `n/4`, so
some matching choice has at most `n/4` bad vertices. Delete one of the
two selected edges at each bad vertex. At most `n/4` physical edges
are deleted (possibly fewer if one deletion repairs two vertices), and
deletion cannot create a capacity violation. The remaining one-color
set is feasible and has at least `3n/4` edges. Since the graph has
`2nN` physical edges, the claimed equal-count barrier follows.

The random alternating choices are binary variables, one per cycle
of each factor. At a vertex the sole potentially forbidden choice is
one assignment of its `H`-cycle and `M`-cycle variables, so full local
pair synchronization is a signed bipartite 2-CNF system. Even a dense
or highly frustrated constraint graph cannot force the all-equal
count certificate past `4/3`: a random assignment violates at most a
quarter of its clauses in expectation, and one deletion per violated
vertex suffices.

This argument does not preserve prescribed frequencies of the edge
types across colors. In particular it does not show
`chi'_w(G_N)≤(8/3)N`. A dual profit vector concentrated on selected
types may still expose a stronger local/global gap. Weighted repair
would need to keep at least `3/8` of the total type profit in some
feasible color; the deletion proof guarantees only the unweighted
count. The known `K4,4` shared-guard example gives an unequal-profit
gap `7/6`, but no example above `4/3` is established here.

## A direct obstruction to unweighted 2-lift amplification

Take a graph `G` in this class and any two-sheet graph lift, twisting
edges arbitrarily, while preserving each lifted edge's base weight and
physical multiplicity. Every feasible base color pattern lifts to one
feasible color on the cover: include both lifts of each selected
physical edge. Each lifted vertex sees exactly the same load as its
base vertex. Thus **any base coloring lifts with the same palette**,
and the cover cannot have a larger chromatic number than the base for
the same per-type multiplicity. Its local bin-packing number is also
the same as the base, since each lifted star is identical. Therefore
an inherited-weight 2-lift of the `K4,4` example cannot amplify its
`7/6` ratio, regardless of twist signs.

The script `uniform_factor_polar_cutting.py` independently computes
the uniform-demand polar gap using a linear master problem and exact
integer weighted-color-pattern separation. It returns `7/6` for the
base 16-type example and for one arbitrary twisted 32-type lift.
A locally pairable small perturbation of the lifted weights also
returned `7/6`; that single perturbation is diagnostic only.
