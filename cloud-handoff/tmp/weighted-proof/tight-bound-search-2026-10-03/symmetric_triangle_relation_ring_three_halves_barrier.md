# A scalable symmetric triangle-relation ring cannot beat 3/2

**Scope.** This is a proved one-color configuration-gap statement for
the symmetric profit directions of one proposed gadget family. It is
not a 3/2 theorem for arbitrary asymmetry or arbitrary weighted graphs.

Let `k>=3` and arrange `k` mutually disjoint heavy blocker edges of
weight `h in (1/2,1]` in a cycle. Each blocker has two ports, one
appearing in each neighboring relation. Between a port of blocker `i`
and a port of blocker `i+1`, put a unit direct edge `P_i`. Add a new
hub `c_i` with divisible fluid edges from both ports to `c_i`. Thus
each relation is a triangle, and the blocker edges connect the
triangles in a ring. The ring length can be odd.

Give every heavy blocker profit `a>=0`, every direct edge profit
`b>=0`, and every unit of fluid profit one. Rotational and reversal
symmetry permit a local optimum with common means `x` on blockers,
`p` on direct edges, and `y` on each of the two fluid spokes of a
relation. The exact local feasibility conditions are

    x+p <= 1,       h*x+p+y <= 1,       2*y <= 1,
    x,p,y >= 0.                                             (1)

The first two inequalities are exactly the convex hull of the states
at a port (heavy present, direct unit present, or neither, followed
by up to the residual fluid capacity); the last is the hub capacity.
The local objective divided by `k` is `a*x+b*p+2*y`.

At a local-polytope vertex there are only six nonzero possibilities:

    (1,0,0), (0,1,0), (0,0,1/2),
    (1,0,1-h), (0,1/2,1/2), (1/(2h),0,1/2).

The first, second, fourth vertices are directly matched or dominated
by global colors with all blockers present or all absent. The third
has local value `k` and a no-blocker fluid color also has value `k`.
The fifth has local value `k(b/2+1)`; a no-blocker color has value
`k*max(b,1)`, and `b/2+1 <= (3/2)max(b,1)`.

For the last vertex the local value is `k(1+a/(2h))`. If `a<=h`,
this is at most `3k/2`, and a no-blocker fluid color has value `k`.
If `a>=h`, an all-blocker color carries `2(1-h)` fluid in each
relation, worth `k(a+2(1-h))`. The desired comparison follows from

    (3/2)(a+2(1-h)) - (1+a/(2h))
      = a(3/2-1/(2h)) + 2-3h
      >= (3/2)(1-h) >= 0.

Therefore every symmetric nonnegative-profit direction has local
support at most `3/2` times the global one-color optimum, for every
`k` and every `h>1/2`. It is not necessary to enumerate the `2^k`
blocker-state patterns. The useful global states are simply *all
blockers absent* and *all blockers present*, so odd-cycle frustration
of the intermediate states cannot strengthen this symmetric route.

For context, fixing a blocker-state bit `z_i` gives relation reward
`f(0,0)=max(b,1)`, `f(0,1)=f(1,0)=1`, and
`f(1,1)=2(1-h)`. When `1<b<2h`, the direct edge rewards both-free
ports while the star generates an antiferromagnetic pair preference.
The inequalities above show that this apparent competing-correlation
mechanism does not defeat the all-absent/all-present palette states.
Asymmetric profits and higher-rank spokes are not covered.
