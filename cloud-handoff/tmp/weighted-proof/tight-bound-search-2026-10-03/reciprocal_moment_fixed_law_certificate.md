# Exact fixed-law reciprocal certificate (2026-10-03)

This proves a **restricted** slice of the unresolved independent two-star moment inequality. It does not prove that the fixed law is extremal among all feasible stars or moment laws.

Normalize the boundary case `y=0,D_u=D_v=1` so each competitor sum has mean 1 and second moment at most `4/3`. The target becomes

`E[1/max(3/4,X,Y)] >= 3/4`.

Fix one independent variable `X` to have law `P(X=0)=1/4`, `P(X=4/3)=3/4`; this saturates `EX=1`, `EX²=4/3`. For **every** independent nonnegative `Y` with `EY=1`, `EY²<=4/3`, there is the stronger exact lower bound

`E[1/max(3/4,X,Y)] >= 19/25 = 0.76`.

Indeed, conditioning on `Y=y` gives

`psi(y)=43/48` for `0<=y<=3/4`,

`psi(y)=9/16+1/(4y)` for `3/4<=y<=4/3`, and

`psi(y)=1/y` for `y>=4/3`.

The simple quadratic

`q(y)=22/25+(2/25)y-(3/20)y²`

satisfies `q(y)<=psi(y)` for every `y>=0`. On `[0,3/4]`, the maximum of `q` is `334/375<43/48`. On `[3/4,4/3]`, multiplying `psi-q` by `400y` gives `100-127y-32y²+60y³`. With `t=y-1 in [-1/4,1/3]`, this is `1-11t+(148+60t)t² >=1-11t+133t²>0`. On `[4/3,infinity)`, multiplying `psi-q` by `100y` gives `100-88y-8y²+15y³`. With `t=y-8/5 >=-4/15`, this is `4/25+(8/5)t+(64+15t)t² >=4/25+(8/5)t+60t²>0`. Taking expectations and using the second-moment upper bound gives `E psi(Y)>=22/25+2/25-(3/20)(4/3)=19/25`.

Numerical alternating moment LPs put the global boundary minimum near `0.7626`, often with this two-point law on one side. Yet this law is **not** universally worst against each feasible opponent: on a grid, a feasible two-point opponent near `Y=0.04` (probability 0.2441), `Y=1.31` (probability 0.7559) makes the best-response X-law a three-point law near `(0.29,1.02,1.56)`, with value about `0.76677`, while the fixed two-point X-law gives about `0.78953`. Thus a proof of the unrestricted moment theorem needs to handle changing optimal support; the fixed-law certificate is only a useful local anchor.

A separate naive nested-envelope bound fails: optimizing the Y-law independently for each realized x, then optimizing X, gives about `0.7358` on fine grids, below `3/4`. It discards the common, independent Y-law and cannot prove the desired inequality.
