# A shared-guard synchronization gap on bipartite K4,4

**Exact construction; not a lower bound above 4/3.** This gives a
different mechanism from the private-guard graded path: all heavy
edges have two nonprivate core endpoints, and locally optimal pairings
cannot be synchronized into only `bp` global colors. Its ratio is
`7/6`, so amplification is still needed to beat the existing `4/3`
family.

Let left vertices be `L_0,...,L_3` and right vertices `R_0,...,R_3`,
with subscripts modulo four. There are 16 edge types, partitioned into
two edge-disjoint C8 factors of K4,4:

    H_i = L_i R_i       (i=0,1,2,3),
    H_{4+i} = L_i R_{i+1},
    M_i = L_i R_{i+2},
    M_{4+i} = L_i R_{i+3}.

Give the eight heavy types `H_0,...,H_7` weights

    (34,32,36,32,38,34,34,34)/60,

and the eight medium types `M_0,...,M_7` weights

    (22,28,26,26,24,26,22,26)/60.

Replace each type by `N` parallel physical edges. Each heavy weight is
above `1/2`; each medium weight is in `(1/3,1/2)`. The resulting
multigraph is bipartite.

## Exact local bound

At every vertex there are `2N` heavy edges, so at least `2N` bins are
needed. The following table pairs the two incident heavy types with
the two incident medium types, each pair having total weight at most
one. Repeat each pairing `N` times:

| Vertex | Two local pairs |
| --- | --- |
| `L_0` | `H_0 M_4`, `H_4 M_0` |
| `L_1` | `H_1 M_1`, `H_5 M_5` |
| `L_2` | `H_2 M_6`, `H_6 M_2` |
| `L_3` | `H_3 M_3`, `H_7 M_7` |
| `R_0` | `H_0 M_2`, `H_7 M_5` |
| `R_1` | `H_1 M_3`, `H_4 M_6` |
| `R_2` | `H_2 M_0`, `H_5 M_7` |
| `R_3` | `H_3 M_1`, `H_6 M_4` |

Thus `bp(G_N)=2N`.

## Seven-type lower certificate

Put unit profit on precisely

    S={H_1,H_3,H_4,H_5,H_6,M_1,M_4},

and zero profit on other types. Every feasible color has profit at most
three. Here is a direct check. The five selected heavy types form a
graph with matching number three, so no color contains four of them.
If one `M_1` occurs, it excludes `H_5` at `L_1` and `H_6` at `R_3`;
the remaining selected heavies have matching number two. If one
`M_4` occurs, it excludes `H_4` at `L_0`, and the remaining selected
heavies have matching number two. If both medium types occur, they
occupy `52/60` at `R_3`, excluding `H_3,H_6`; `M_1` excludes `H_5`
and `M_4` excludes `H_4`, leaving only `H_1` among the selected
heavies. Two copies of `M_1` exclude all selected heavies incident
to `L_1` or `R_3`, leaving at most `H_4`; two copies of `M_4` exclude
those incident to `L_0` or `R_3`, leaving at most one of `H_1,H_5`.
Three selected medium edges cannot fit at `R_3`, since each weighs at
least `24/60` there. These cases cover all nonnegative integer color
patterns, including two occurrences of the same edge type.

There are `7N` physical edges of selected types. Hence

    chi'_w(G_N) >= ceil(7N/3).

## Matching coloring when 3 divides N

The following six feasible color patterns cover every edge type
exactly three times when `P_1` is counted twice and each other pattern
once. An entry `2M_i` means two different physical edges of type `M_i`
in that color.

| Pattern | Heavy types | Medium types | Copies in coloring |
| --- | --- | --- | --- |
| `P_1` | `H_4,H_5,H_6,H_7` | `M_5,M_6,M_7` | `2N/3` |
| `P_2` | `H_2,H_4,H_7` | `M_0,2M_1,M_6` | `N/3` |
| `P_3` | `H_1,H_3` | `M_0,2M_2,M_3,M_4` | `N/3` |
| `P_4` | `H_0,H_5,H_6` | `M_2,M_3,M_4,M_7` | `N/3` |
| `P_5` | `H_0,H_1,H_2,H_3` | `M_3,M_4,M_5` | `N/3` |
| `P_6` | `H_0,H_1,H_2,H_3` | `M_0,M_1` | `N/3` |

Direct endpoint summation shows every pattern has load at most `60/60`
at all eight vertices. Allocate the `N` copies of each type across
the listed colors according to its three pattern occurrences. There
are `7N/3` colors, so for every positive `N` divisible by three,

    bp(G_N)=2N,     chi'_w(G_N)=7N/3,
    chi'_w(G_N)/bp(G_N)=7/6.

The exact ratio remains `7/6` in the asymptotic fractional sense. It
is lower than the known `4/3` construction, but it confirms that
sharing heavy endpoints creates a genuine local/global consistency
obstruction on a bipartite support. The private-guard forest theorem
and the balanced private-guard cycle barrier do not cover this family.

## Search provenance

`bipartite_shared_guards_k44.py` defines the factor support and the
finite configuration LP search. Its log records 40 heterogeneous
locally pairable random instances with no ratio above `4/3`; that
heuristic search did not by itself locate the exact example. A separate
deterministic seed-99 random scan found the above locally pairable
weights with no compatible pair of full heavy and medium matchings.
The seven-type dual certificate and six-pattern coloring above verify
the result independently of numerical optimization.

## Why a single medium matching cannot scale this mechanism

Suppose the heavy edges instead form any bipartite 2-regular multigraph,
with `N` copies of every heavy edge, and the medium edges form a matching,
also with `N` copies of every edge and weights at most `1/2`. Color the
heavy 2-factor in `2N` ordinary matching colors by König's theorem.
The medium matching needs only `ceil(N/2)` additional weighted colors:
put two physical copies of each medium edge in each such color, and
delete any excess in the last color. Each vertex has `2N` incident
heavy copies, so `bp>=2N`. Consequently

    chi'_w/bp <= (2N+ceil(N/2))/(2N) = 5/4+O(1/N).

Thus replacing the second medium factor by isolated shared chords
cannot beat `4/3`, no matter how their compatibility with the heavy
edges is arranged. This bound uses an explicit coloring and permits
heterogeneous heavy weights above `1/2` and medium weights at most
`1/2`.
