# Three pairs disprove simultaneous width-two control of all fluid-star prefixes

**Scope:** This refutes a convenient *sufficient coupling condition* for the
single-star half-gap, not the half-gap itself. The latter is already proved
by the independent-flow construction in
`../arbitrary-density-fluid-star-half-deficit.md`.

Let three pair residuals be `R_0=A`, `R_1=(3/5)B`, and `R_2=C`, where
`A,B,C` are Bernoulli variables with prescribed probabilities

`P(A=1)=4/5`, `P(B=1)=1/5`, `P(C=1)=1/2`.

Their joint law is free to choose. Order the six fluid-star leaves by
decreasing density in the pair sequence

`0, 1, 1, 2, 2, 0`.

The six cumulative leaf-capacity sums are

`A`, `A+3B/5`, `A+6B/5`, `A+6B/5+C`,
`A+6B/5+2C`, `2A+6B/5+2C`.

There is **no** coupling of the three prescribed marginals for which
all six random sums simultaneously have essential range at most two.

Here is a finite exact certificate. Label the eight deterministic binary
states by the three-bit string `ABC`. Two states can coexist in a
width-two coupling only if their six displayed prefix values differ by
at most two at every position. Direct rational comparison gives exactly
these maximal sets of mutually compatible states:

| Maximal compatible state set | Contradiction with the required means |
|---|---|
| `101,110,100` | `A=1` surely, but `E A=4/5` |
| `101,110,111,011` | `A=0` requires state `011` with mass `1/5`; that uses all of the required `B=1` mass, forcing `C=1` surely |
| `101,001,100` | `B=0` surely, but `E B=1/5` |
| `101,001,011` | `C=1` surely, but `E C=1/2` |
| `000,100,001,010` | `C=1` implies `A=0`, hence `E C<=1-E A=1/5` |
| `010,110,100` | `C=0` surely |
| `010,110,011` | `A=1` implies `B=1`, hence `E A<=E B=1/5` |
| `010,001,011` | `A=0` surely |

Any support with width at most two is a subset of one of these maximal
compatible sets, and none permits the prescribed marginal means.
Thus the obstruction is exact; the search program
`upper_prefix_width_search.py` merely found the certificate.

The means of the six prefixes are `4/5,23/25,26/25,77/50,51/25,71/25`.
Only the second and third prefixes straddle the cap at one. The
cap-at-one Jensen gaps increase until that crossing and decrease
afterward, so a coupling need control **only those two prefixes** to
obtain the half-gap. In fact, counterquantile coupling of the other
terms with the active pair makes those two widths at most two. This
explains why the true half-gap survives the counterexample.
