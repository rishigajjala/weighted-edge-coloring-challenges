# Exact obstruction to a moment-only proof

Interim research note, 3 October 2026. This refutes a relaxation of the
two-star inequality, **not** the actual independent-star inequality or a
weighted edge-coloring bound.

At endpoint parameters D_u=D_v=1 and probe target y=0, the proposed
moment relaxation has EX=EY=4/3, Var(X),Var(Y)<=16/27, support in
[0,16/3], and requires E[1/max(1,X,Y)]>=9/16. Even adding Cov(X,Y)=0
does not suffice.

Use the following symmetric joint law:

| (X,Y) | Probability |
|---|---:|
| (0,0) | 392/3969 |
| (5/6,2) | 64/147 |
| (2,5/6) | 64/147 |
| (36/11,36/11) | 121/3969 |

The probabilities sum to one. Direct arithmetic gives

    EX=EY=4/3,
    EX^2=EY^2=64/27,
    EXY=16/9.

Thus both variances are exactly 16/27 and the covariance is zero.
Nevertheless,

    E[1/max(1,X,Y)]
      =392/3969 + 64/147 + (121/3969)(11/36)
      =77651/142884 <9/16.

This is not an artifact of a zero probe target. For y=1/100, keep
D_u=D_v=1, put X'=(99/100)X, Y'=(99/100)Y and b=1/75. The required
means are now 33/25, and the scaled variances are no larger than the
allowed (99/100)(16/27). Covariance remains zero. The reciprocal value is

    392/3969 + (128/147)(150/299) + (121/3969)(825/2684),

which is still less than 9/16. Thus a positive, uncapped probe also
defeats the covariance-only relaxation.

The law is not independent: it has positive mass at (0,0) but no mass
at (0,2), while both marginal values have positive mass. The actual
two-star variables are independent and satisfy additional Bernoulli-sum
structure. Those facts cannot be discarded in a proof. Floating LP
diagnostics also found failures after adding some mixed moments of
bidegree at most (2,2); those diagnostics have no exact certificate here.
