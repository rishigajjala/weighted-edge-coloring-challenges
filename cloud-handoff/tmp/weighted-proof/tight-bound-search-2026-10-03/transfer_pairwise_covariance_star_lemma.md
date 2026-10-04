# Pairwise covariance is enough for private-pair star completion

**Status: proved scalar transport lemma.** This weakens the
independent-base hypothesis in
`upper_arbitrary_paired_star_forest_half_deficit.md`. It is a
potential interface to favorable heavy-matching laws, not a theorem
that every matching law has the required covariance signs.

Let `Z_1,...,Z_m in [0,1]` have an arbitrary prescribed **joint** law
with `Cov(Z_i,Z_j)<=0` for every `i≠j`, and put `U=sum_i Z_i`.
Let private variables `Y_1,...,Y_k in [0,2]` have arbitrary
prescribed one-dimensional laws. If

`E U+sum_i E Y_i<=1`,                              (1)

then the `Y_i` can be coupled with the existing complete joint law
of the `Z_i` so that

`E(U+sum_i Y_i-1)_+<=1/2`.                          (2)

**Proof.** The pointwise inequality

`(sum_i z_i-1)_+<=sum_{i<j}z_i z_j`

for `z_i in [0,1]` is proved by the induction in the earlier note.
Taking expectations under pairwise nonpositive covariance gives

`E(U-1)_+<=sum_{i<j}E Z_i E Z_j<=(E U)^2/2`.    (3)

This is the *only* place the earlier proof used independence among
base summands. If one private two-point variable is `Y=a+dB`,
add the deterministic `a` as another `[0,1]` summand. When `d<=1`,
sample `B` independently of the whole base vector; all old
nonpositive pairwise covariances remain, new covariances are zero,
and (3) proves (2). When `1<d<=2`, couple `B=1` to the lowest
probability `p=E B` of the scalar base sum. The lower-tail average
is at most the unconditional average, and (3) gives exactly the
bound `1/2+(1-m)^2(1/2-1/d)<=1/2`, with `m=EU+a`, from equation
(6) of the earlier note. Convexity of the minimum transport value
in the private variable's law and mean-preserving finite-grid
approximation extend this to every prescribed `Y in [0,2]`.

For many private variables, counterquantile-couple them into an
aggregate of width at most two, shift its essential lower endpoint
`a<=1` into the base as a deterministic summand, apply the
one-variable result, and lift through the conditional law of the
private vector given its aggregate. Throughout, disintegration
preserves the **entire original joint law** of the base vector.
This proves (2). `□`

For a fluid star, the base summands are the preliminary singleton
leaf flows and `1-(1-c)X` from the hub residual after reserving its
possible own-partner edge. If their joint law has the pairwise
covariance signs above, the same proportional trimming gives
expected hub and leaf deficits at most `1/2`. The base laws of
different stars may be correlated arbitrarily, provided one
globally consistent law has the required signs separately within
every star. Private pair variables belong to one star, so their
conditional kernels still glue around cycles of shared pairs.

This condition is sufficient, not automatic for an arbitrary
heavy-matching decomposition. Negative dependence of heavy edge
indicators may give favorable covariance among residuals at
different leaves, but a hub-vacancy term can reverse the sign,
and two leaves joined by a heavy edge share one indicator. These
issues must be checked before invoking this lemma in an
arbitrary-heavy-plus-fluid argument.
