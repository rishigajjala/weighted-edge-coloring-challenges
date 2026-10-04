# Uniform-rank triangle factors still have gap at most 3/2

This is a scoped theorem for a repeated-spoke factor model. It
includes the equal-weight rank-one case and approaches the divisible
spoke model as the rank grows, but excludes mixed spoke sizes
whose hub packing law is not a single count capacity.

Let blocker edges form a matching; their weights and profits may be
arbitrary. Deleting blockers leaves vertex-disjoint triangle factors.
In one factor, the two ports `a,b` are connected by a unit direct edge
of profit `q>=0`; each port is connected to a private hub `c` by a
bundle of at least `k` identical spokes. All spokes in this factor
have a common weight `s` with `floor(1/s)=k`, and profits per spoke
are `u/k` on side `a` and `v/k` on side `b`. Thus either port and the
hub can hold at most `k` spokes when no direct edge is present. Each
port has at most one incident blocker, and the two ports touch
distinct blockers. When its blocker is selected, port `i` has room
for `r_i` spokes, `0<=r_i<=k`. Put `H_i=(k-r_i)/k`.

**Claim.** The maximum global one-color profit is at least `2/3` of
the vertex-local configuration relaxation optimum, regardless of
cycles or branching in the blocker-factor network.

Normalize spoke counts by `k`, writing their means `L,R`; let `x,z`
be the two blocker means and `p` the direct-edge mean. Exact
vertex-local feasibility is

    0<=p<=1-max(x,z),
    0<=L<=1-p-H_a*x,
    0<=R<=1-p-H_b*z,
    L+R<=1.                                            (1)

Independently select blockers with probabilities `2*x/3,2*z/3`
and optimize the factor conditional on the selections. Conditional
optima are actual integer spoke counts: because all spokes have the
same weight, greedy filling of at most `k` slots is integral. Factors
are disjoint, so these choices combine globally. Blocker profit
scales exactly by `2/3`.

To compare expected factor profit `E` with the local optimum `g`,
exchange sides so `u>=v`. Conditional optimum profits are linear in
`(q,u,v)` on each cone `q>=u>=v` and `u>=v,u>=q`, whereas `g` is
convex and homogeneous. The five generating rays are

    (q,u,v)=(1,0,0),(0,1,0),(1,1,0),(0,1,1),(1,1,1).

For direct-only, `g=1-max(x,z)` and
`E=(1-2*x/3)(1-2*z/3)>=2g/3`. For the left-spoke-only and
direct-plus-left-spoke rays, `g=1-H_a*x` and
`E=1-(2/3)*H_a*x>=2g/3`.

For both-spokes and all-three rays, the conditional factor profit is
one if at least one blocker is absent. If both are present, it is
`min(1,2-H_a-H_b)`. Put

    delta=(H_a+H_b-1)_+,   T=H_a*x+H_b*z.

Then both rays have `E=1-(4/9)*delta*x*z`. If `delta=0`, this is
one. The two-spokes local value is at most one; the all-three local
value is at most `3/2` because
`p+L+R<=p+min(1,2-2*p)<=3/2`. Thus both inequalities hold.

If `delta>0`, then `H_a+H_b=1+delta` and `delta<=1`. Since
`x,z<=1`,

    T >= (H_a+H_b)*x*z = (1+delta)*x*z >= 2*delta*x*z,

so `E>=1-2*T/9`. For the two-spokes ray,
`g=min(1,2-T)`. If `T<=1`, then `E>=7/9>2g/3`;
if `T>=1`, then

    E-(2/3)*g >= -1/3+4*T/9 >= 1/9.

For the all-three ray, fixing `p` leaves spoke total at most
`min(1,2-T-2*p)`, whence

    g <= max_p min(1+p,2-T-p) <= 3/2-T/2.

Therefore `E>=1-2*T/9>=1-T/3>=2g/3`. All five rays are proved,
and summing the factor inequalities proves the claim.

Uniform rank can still realize an internal `3/2` triangle gap:
at blocker means zero, take direct profit `q=1`, each spoke profit
`1/k`, and local means `p=1/2`, `L=R=1/2`. The local value is
`3/2`, while the global factor value is `1`. Repeating equal-size
spokes therefore does not by itself compound this gap beyond `3/2`.
Mixed spoke weights, nonuniform capacities at the same hub, and
factors with three or more blocker ports remain outside the theorem.
