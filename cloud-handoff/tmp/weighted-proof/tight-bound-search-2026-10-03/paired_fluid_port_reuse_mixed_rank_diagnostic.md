# Port-reusing blocker correlation gadget: exact small diagnostics

**No lower bound above `4/3` was found here.** The purpose was to
test a concrete escape from the parity barrier in
`paired_fluid_relation_port_parity_barrier.md`: a fluid edge can prefer
aligned heavy-free states, while two spokes at a fixed hub can prefer
dispersed free states. The smallest three-blocker relation triangle
that reuses one blocker port was evaluated in both the divisible-fluid
and physical multi-rank models.

## Divisible-fluid model

Take heavy matching pairs `A=(L0,R0)`, `B=(L1,R1)`, `C=(L2,R2)` with
weights `h_A,h_B,h_C`. Add a fixed left hub `X`. Fluid edges are
`L0-R1`, `L1-R2`, `X-R0`, and `X-R2`. The last two spokes compete at
`X`; the second direct edge and last spoke reuse `R2`.

For fixed local means `(x,y)`, global scaled membership is one LP with
probabilities on the eight heavy states and state-conditioned fluid
flows. The LP enforces exact scaled heavy marginals and exact scaled
fluid means, with statewise capacity `1-h_i z_i` at both pair ports.
Thus the test optimizes blocker correlations; it does not impose
independence. A dummy fourth pair with zero target demand represents
the fixed hub in `paired_fluid_three_pair_c6_gauge.py`.

All vertices of the exact local mean polytope were enumerated by
halfspace intersection for each of four templates:

| Heavy weights `(A,B,C)` | Local vertices | Smallest global `alpha` | Gap |
| --- | ---: | ---: | ---: |
| `(.5001,1,1)` | 60 | `.8000000064` | approximately `5/4` |
| `(.6,1,.6)` | 92 | `.8064516129` | `1.24` |
| `(.55,.8,1)` | 100 | `.8533333333` | `1.171875` |
| `(.75,.75,.75)` | 111 | `.9` | `10/9` |

The worst point for `(.5001,1,1)` reduces to the known one-fluid-edge
two-blocker path. All LP results are numerical, although the finite
support and state constraints are exact descriptions of the specified
divisible model.

Dense off-diagonal fluid supports on three, four, and five heavy pairs
were also tested. For the three-pair K3,3 support, every local vertex
was enumerated for 56 symmetric weight triples from
`{.5001,.55,.6,.7,.8,1}`; maximum observed gap was `5/4` and again
used just one fluid edge. Four- and five-pair tests sampled hundreds
to thousands of local LP vertices per weight template, without a gap
above `5/4`. Those latter tests are not exhaustive.

## Physical multi-rank model

`bipartite_hybrid_port_frustration_polar.py` gives each of the seven
physical bundles a fixed integer-hundredth weight. It enumerates all
globally feasible count patterns, all local integer knapsack patterns,
and all vertices of the nonnegative-profit polar. The global pattern
types allow repeated copies of a bundle; the local LP matches only
mean counts across its two endpoints. For six structured templates,
the maximum local/global profit ratios were:

| Heavy `(A,B,C)` | Other four weights | Full-profit gap |
| --- | --- | ---: |
| `(51,100,100)` | `(49,49,49,49)` | `5/4` |
| `(51,100,100)` | `(40,26,26,40)` | `5/4` |
| `(60,100,60)` | `(40,26,26,40)` | `5/4` |
| `(60,100,60)` | `(34,26,26,34)` | `5/4` |
| `(60,100,60)` | `(26,26,26,26)` | `11/9` |
| `(51,100,100)` | `(34,26,26,34)` | `5/4` |

All best `5/4` profit vectors assign zero profit to every type outside
one two-heavy/one-medium subpath. Thus merely adding this port reuse
and several rank-three edge types does not amplify the two-blocker
obstruction. These are finite-template calculations using floating
Qhull/HiGHS; a positive result would require rational checking, but
none exceeds the already established bipartite `4/3` lower bound.
