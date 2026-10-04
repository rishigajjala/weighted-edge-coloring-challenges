# Two crossing prefixes suffice for the known arbitrary-density star half-gap

**Status:** Complete independent proof of the scalar single-star inequality
already established by `../arbitrary-density-fluid-star-half-deficit.md`.
This is a shorter proof for the scalar support function, not a new
unrestricted graph theorem. It also explains why simultaneous control
of every prefix's support width is unnecessary.

Let a fluid star have hub capacity `X in [0,1]`, fixed at one or equal
to the residual of one discrete pair. Every other discrete pair `i`
supplies a common residual `R_i in [0,1]` to its two vertices, with
arbitrary prescribed marginal law. Other leaves have fixed capacity
one. The residuals of distinct pairs may be coupled freely.

Sort fluid edges by nonincreasing density `rho_1,...,rho_m`, set
`rho_(m+1)=0`, and write `S_j` for the sum of capacities of the first
`j` leaves. The optimum profit is

`F = sum_j (rho_j-rho_(j+1)) min(X,S_j)`.

Its all-capacity-one value is `A=rho_1`. Put

`D_j=S_j-X`, `mu_j=E D_j`, and
`g_j=min(E X,E S_j)-E min(X,S_j)`.

Since `min(X,S)=X+min(0,S-X)`, the gap satisfies exactly

`g_j=E(D_j)_+` if `mu_j<=0`, and
`g_j=E(-D_j)_+` if `mu_j>=0`.             (1)

The sequence `D_j` increases pointwise. Thus `g_j` increases along
prefixes with `mu_j<=0` and decreases along prefixes with `mu_j>=0`.
Only the two prefixes adjacent to the crossing of mean hub capacity
can have maximal gap. If there is no crossing, just the last prefix
(all means below) or first prefix (all above) needs control.

At a crossing, let the newly added leaf have residual `R` from an
external discrete pair. It was seen `a in {0,1}` times previously.
Write `S_-=T+aR`, `S_+=T+(a+1)R`; no other coefficient changes.
In `T-X`, each residual from another external pair occurs with
coefficient `0,1,2`, while the hub's own pair residual `X`, if its
partner leaf has already appeared, cancels with the `-X` term.
Counterquantile-couple the external terms in `T` sequentially; their
sum `U` has essential support width at most two. If the partner leaf
is absent, comonotone-couple `U` with `X`, making `U-X` have width at
most two. If that leaf is present, `T-X=U` already has width at most
two. Finally counterquantile-couple `T-X` with `R` and lift this joint
law through the conditional law of all earlier variables given `T-X`.
The two crossing differences are

`D_-=(T-X)+aR`, `D_+=(T-X)+(a+1)R`.

Opposite quantiles make **both** their support widths at most two:
the coefficient on `R` is either one or two and the other summand's
width is at most two. This coupling preserves every pair marginal.

If the crossing leaf is the hub's own partner, then `S_+=S_-+X` and
`min(X,S_+)=X` pointwise, so `g_+=0`. The preceding balancing of
`S_--X` controls the sole relevant gap. The no-crossing endpoint
cases are handled by the same balancing (or are immediate for a
single first leaf).

For any concave hinge `min(0,Z)` and a variable `Z` of support width
at most two, its Jensen gap is at most one half. Indeed
`gap=(E|Z|-|E Z|)/2 <= E|Z-E Z|/2 <= width(Z)/4`.
Consequently the relevant gaps are at most `1/2`; monotonicity (1)
gives `g_j<=1/2` for *all* `j`. Summing with nonnegative density
increments yields

`E F(R) >= F(E R)-A/2`.

The counterexample in `upper_all_prefix_width_counterexample.md`
shows why one cannot generally require the stronger property that
**every** prefix itself have width at most two under one coupling.
