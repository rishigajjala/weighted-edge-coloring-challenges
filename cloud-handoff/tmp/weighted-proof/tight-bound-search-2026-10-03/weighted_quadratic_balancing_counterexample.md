# Squared-load minimization does not prove weighted range two

This is an exact counterexample to a proposed proof method, not to the
range-two existence statement. It explains why the proved binary
alternating-trail argument cannot simply replace binary incidences by
arbitrary real ones while keeping its quadratic potential.

## Construction

Let `H` be the nine-dimensional cube, with `m=512` vertices and degree
`d=9`. Add one root `r`. Make a real matrix with rows indexed by the root
and the cube vertices. Its columns have exactly two nonzero entries:

* For each vertex `v` of the cube, a port column has entry `5/1024` at
  the root and entry `1` at `v`.
* For each cube edge `uv`, a column has entry `-1/9` at both `u` and `v`.

All entries lie in `[-1,1]`. For signs `sigma` on the columns, minimize
`||A sigma||_2^2`. We prove that the only minimizers assign the same sign
to every column. Both minimizers have root discrepancy `5/2>2`.

If every sign is positive, the root sum is `512*(5/1024)=5/2`, and
each cube-vertex sum is `1-9/9=0`. The energy is therefore `25/4`.

## Energy of any other signing

Let `t_v` be the port sign at `v`, and `q_e` the cube-edge sign. Define
`k_v` as the number of cube edges incident to `v` with `q_e != t_v`.
The cube-vertex discrepancy is exactly

    t_v - (1/9) sum_{e incident v} q_e = (2/9) t_v k_v.

Let `S` be a smaller port-sign class and put `s=|S|<=256`. Every cube
edge crossing between the two port-sign classes disagrees with the port
sign at exactly one endpoint. Consequently

    sum_v k_v >= |boundary_H(S)| >= s.

The last inequality is proved below. Since `k_v` is a nonnegative integer,

    internal energy = (4/81) sum_v k_v^2 >= 4s/81.

The magnitude of the root sum is `(5/1024)(512-2s)`. Compared with the
all-positive signing, the decrease in its squared value is

    (5/1024)^2 [512^2-(512-2s)^2]
      = (25/262144) s(512-s)
      <= 25s/512.

But `4/81>25/512`, since `2048>2025`. Thus every signing with `s>0`
has energy strictly greater than `25/4`. If `s=0`, all port signs agree;
zero internal energy requires every cube-edge sign to agree with them.
This proves the assertion about all global minimizers.

## Elementary cube cut bound

For every subset `S` of the `d`-cube, its edge boundary has size at least
`min(|S|,2^d-|S|)`. Prove this by induction, reducing by complementation
to `|S|<=2^{d-1}`. Split the cube into two `(d-1)`-cubes and write
`a,b` for the corresponding subset sizes. The boundary is the sum of
the two within-layer boundaries and the symmetric-difference size
between the layer subsets, the latter at least `|a-b|`.

If `a,b<=2^{d-2}`, induction already bounds the within-layer sum by
`a+b`. Otherwise suppose `a>2^{d-2}>=b`. Induction and the cross-layer
bound give at least

    (2^{d-1}-a)+b+(a-b)=2^{d-1}>=a+b.

The one-dimensional case is immediate.

## The same example as two-state source lists

Each column becomes one source, with two states. For a port source
use states `(5/1024,1)` and `(0,0)`. For a cube-edge source use states
`(0,0)` and `(1/9,1/9)`. Assigning its states to two colors chooses the
sign of its difference column. Each source permutation is used at both
endpoints, as required in the shared-source model.

At each row the sum of the two color loads is fixed. Therefore the
total squared-load potential equals a fixed constant plus
`(1/2)||A sigma||_2^2`. Every global minimizer of that potential has
root color-load difference `5/2` and fails the proposed bound two.

Nevertheless this instance has an explicit good assignment. Set port
signs by the first cube coordinate, so half are positive and half
negative. Give every cube edge within a coordinate layer its layer's
sign; give the edges between layers positive signs. The root discrepancy
is zero. At positive-layer vertices it is zero, and at negative-layer
vertices it is `-2/9`. Thus the largest absolute discrepancy of this
assignment is only `2/9`. Its larger quadratic energy is exactly why
the potential selects the wrong assignment.

Two independent agents checked the counterexample and its energy
comparison on 2026-10-03. No numerical optimization or large certificate
is used in the proof.
