# Capacity-two scheduling is sufficient but false for fixed histograms

**Status: proved conditional reduction, physical counterexample to its
scheduling premise, and obstruction to source-freezing induction. This is
not an arbitrary-link integer bound.**

Work in the physical heavy-matching/tiny-star-forest model of
`physical_single_tiny_star_integer_transfer.md`: heavy physical edges have
weight >1/2 and simple support a matching; all other edges have weight at
most `tau<1/2`, with simple support a star forest; `N=bp(G)`. Fix actual
`N`-bin local packings and align each heavy pair's two bin lists by physical
heavy identity. The resulting source has exactly `N` full states. A
permutation of its states assigns each state once to the `N` normal rows,
consistently at both endpoints. An unpaired vertex has its own list.

## 1. Capacity two is sufficient

For a choice of one permutation per source, propose every heavy edge in the
row carrying its identity and every tiny edge in the row carrying its
**leaf-end** local subset. At each tiny-star hub `o`, let `L_o(j)` be the
total proposed heavy-plus-tiny weight in normal row `j`. Every physical
edge is proposed exactly once. Each tiny leaf is locally feasible before
trimming, because its proposed subset came from one actual feasible local
bin with the same heavy identity. Only hubs may be overloaded.

The hub's original local packing gives
`sum_j L_o(j)=total incident physical weight at o <=N`.
If a globally consistent choice of the source permutations satisfies

`L_o(j)<=2 for every tiny-star hub o and every j in [N]`,       (A)

then the chord inequality `(x-1)_+ <=x/2` on `[0,2]` yields

`sum_j (L_o(j)-1)_+ <= (1/2)sum_j L_o(j) <=N/2`

**at every hub simultaneously**. Delete tiny physical edges in each row
until its hub becomes feasible. The deleted weight for one row is at most
its original overload plus `tau`; hence each star loses weight at most
`N/2+tau N`. Pack each star's deleted edges by Next Fit and overlay the
resulting extra palettes across the disjoint tiny-star components. The
number of extra colours is at most
`ceil[(N/2+tau N)/(1-tau)]`. Thus (A) would prove

`chi'_w(G)<=ceil[3N/(2(1-tau))]`

for **arbitrary** heavy links between tiny stars. No dependence on the
number of stars enters this reduction.

The shared source states have an especially useful size restriction. A
source with at most one endpoint in a given tiny star contributes at most
one to that star's proposed row load: it contributes either the hub heavy
load or one leaf subset load. If a heavy pair joins the hub to one of its
own tiny leaves, its *combined* contribution is also at most one. In a
row carrying heavy weight `h`, that leaf's proposed tiny subset has
weight at most `1-h`; in a no-heavy row the hub contribution is zero.
The only source states that can contribute as much as two to one hub are
**private** heavy pairs joining two leaves of the same tiny star. Such a
source touches no other star.

The capacity-two condition (A) would be a strong sufficient scheduling
statement. It is false for fixed local histograms, even at a single
star, as the next section shows. In particular it is not a necessary
bridge to the desired half-deficit bound.

## 2. Physical counterexample to capacity-two scheduling

Take `N=5`, `tau=1/k` for an integer `k` divisible by five and at
least five, and a tiny star with hub `z` and leaves `u,v,w`. Put three physical unit-heavy edges on
`uv`. The simple heavy support is a matching. Put `2k` physical
tiny edges of weight `tau` on each of `uz` and `vz`: at each of `u,v`,
pack `k` of them in each of the two bins carrying no heavy edge. The
aligned private source list joining `u,v` has tiny aggregate

`T=(2,2,0,0,0)`.

Put `k` tiny physical edges of weight `tau` on `wz`, packed
`k/5` per row at `w`. Thus the `wz` total is exactly one and
`Z_j=1/5` in all five rows. At `z`,
the total tiny weight is `2+2+1=5`, and it can be packed in five
unit bins, so `bp(G)=5` (the leaves also have feasible five-bin
packings).

Every row permutation leaves two rows with proposed hub load
`T_j+Z_j=11/5>2`. No globally consistent assignment can satisfy
(A), even though there is just one tiny star and hence no cross-star
permutation conflict. The half-deficit estimate survives: the sum
of hub overloads is `2(11/5-1)=12/5<5/2` before the `tau` trim
allowance. The constant baseline makes a pointwise load cap too
strong; the relevant target is a bound on the **total** positive
part, not on the maximum row load.

## 3. Why robust two-source induction does not extend automatically

The existing 2-degenerate link proof processes a star after at most two
of its incident shared source lists have been fixed. A three-source
version with the same half-deficit is false even for one bipartite tiny
star and actual local-bin histograms.

Take `N=3m`, a hub with three tiny leaves, and each leaf list equal to
one on the same block of `m` rows and zero elsewhere. Let the hub have
no heavy edge, so its residual is one in every row. The sum of proposed
tiny loads has mean one, exactly meeting the hub's volume bound, but it is
three on the common block and zero elsewhere. Its total overload is
`2m=2N/3>N/2`, and condition (A) also fails on that block. With three
lists already fixed there is no private list left to permute, so a
conditional lemma based only on local means and ranges cannot repair it.

This is a literal physical instance: set `tau=1/k` with integer `k>=3`.
On each spoke put `km` tiny physical edges, grouped `k` per active leaf
bin, and join that leaf to a distinct outside vertex by `2m` unit
heavy edges occupying its other bins. Pack all `3km` tiny edges at the
hub in its `3m` bins. The heavy simple support is a matching and the
combined simple support is a tree. Each of the three aligned full source
lists admits the stated fixed permutation. If these were three links
already frozen by an ordering of a larger link graph, the later hub would
have a `2N/3` deficit despite its feasible local packing.

This three-frozen-list example does **not** refute the desired
integer theorem: permuting those lists into disjoint active blocks
gives zero hub overload. It identifies why a source-freezing induction requires a
global permutation invariant once a star can have three previously
fixed links. The previously proved per-star expectation
`N/2+O(sqrt N)` in
`physical_linked_tiny_stars_empirical_transport.md` likewise cannot
supply one simultaneous outcome without a new global selection theorem.

## 4. Abstract obstruction to a two-fixed-source gluing principle

The robust local statement "after any assignment of at most two incident
sources, the remaining sources can be assigned to make this star good"
is not by itself a global consistency theorem when every source touches
at most two stars. A four-vertex cubic link graph gives an exact
counterexample in a binary constraint system.

Put one bit `x_e` on each edge of `K_4`. At each vertex `v`, declare it
good when the XOR of its three incident bits equals a prescribed bit
`b_v`. Choose the four prescribed bits with odd XOR. Every variable
appears in exactly two vertex constraints. For every vertex, after
**any two** of its three incident bits are fixed, the third can be set
uniquely to make that vertex good. Nevertheless no global assignment
makes all vertices good: XORing the four vertex equations cancels every
edge variable twice and gives `0=XOR_v b_v=1`.

This is **not** a physical tiny-star counterexample; the parity-good
relation need not arise as a convex positive-part overload condition.
It proves that the local two-source extension property and the
at-most-two-star incidence of each shared source are logically
insufficient on their own. A full proof must use an additional property
of the actual load/transport cost, such as its one-dimensional order,
convexity, or physical monotonicity, to rule out global frustration.

## 5. Corrected range-two bridge

The failed maximum-load condition (A) can be replaced by a weaker
condition that survives the physical counterexample: require the
`N` proposed loads at **each** tiny-star hub to have range width at
most two,

`max_j L_o(j)-min_j L_o(j)<=2`.                         (B)

Condition (B), if achieved by one globally consistent assignment of
all source permutations, also gives the same uniform integer bound.
Indeed fix a hub and write its load range as `[a,b]`, so
`0<=a<=b`, `b-a<=2`, and its mean `mu<=1`. If `b<=1`, there is no
overload; if `a>=1`, then `mu<=1` forces every load to equal one.
Otherwise `a<1<b`. The chord bound on `[a,b]` gives

`mean_j (L_o(j)-1)_+ <= (b-1)(mu-a)/(b-a)`
`                         <= (b-1)(1-a)/(b-a)`.

Set `u=1-a`, `v=b-1`. Then `u,v>0`, `u+v=b-a<=2`, and the last
expression is `uv/(u+v)<= (u+v)/4<=1/2`. The same trimming and
Next Fit argument as Section 1 applies.

In the Section 2 counterexample, `L=(11/5,11/5,1/5,1/5,1/5)` has
range exactly two, even though its maximum exceeds two. The
one-star theorem constructs (B) by repeated opposite sorting of
source lists. More precisely, aggregate all source lists private to
one star by repeatedly matching the current aggregate in ascending
order to the next list in descending order. Each private two-leaf
list has width at most two, and every other private list has width at
most one, so this gives one private aggregate list `T_o` of width at
most two. If the shared-source lists can first be permuted globally
so that their sum `U_o` has width at most two at **every** star, then
match `T_o` opposite to `U_o` independently at each star. This
preserves every shared source's global assignment and makes the total
`U_o+T_o` have width at most two. Thus the precise missing lemma
concerns only shared sources, each with at most two star coordinates
and each coordinate in `[0,1]`; it is independent of the star means.
For arbitrary heavy links, simultaneous width two for `U_o` remains
**unproved** and is stronger than the actual necessary total-overload
condition. This note does not assert that it always holds.

## 6. Audit of the 2026 weighted-matroid-equitability paper

The primary paper by Bérczi, Liu, Reis, and Tarnawski,
[Weighted Equitability and Matroid-Constrained Discrepancy](https://arxiv.org/html/2608.13983v1), does **not** directly prove
(B). Its Theorem 1 partitions a matroid into `N` bases equitable for
**one scalar weight function**, with range at most the maximum
single-element weight. Its separate matrix theorem rounds **one**
fractional basis for a nonnegative matrix of column sparsity `Delta`
with row error at most `2Delta` times the maximum entry; for
`Delta=2` this is four, and it does not construct a simultaneous
`N`-base partition with range two. Section 8 explicitly asks for
multi-constraint weighted equitability with a bound depending on
column sparsity.

Our shared-state permutation problem fits a special partition-matroid
instance of that open direction. Make each heavy-pair source a block
of `N` elements (its full states). A colour class takes one element
from every block, so it is a basis of the partition matroid. For each
tiny-star hub, give a state element its proposed contribution at that
hub. Each shared element has entries in `[0,1]` in at most two hub
rows, and the desired decomposition into `N` bases asks that each
hub row's base weights have range at most two. Private two-leaf
sources can first be aggregated and added locally by opposite sorting,
so they need not enter this two-sparse global matrix problem.

The paper's localized exchanges control a gap for one weight
function. In this mapping, one exchange changes the weights of up to
two hubs, and their improving directions can conflict. Its weighted
carpooling counterexample concerns **prefix** discrepancy of an
assignment and does not by itself falsify this no-prefix range-two
permutation problem. This is an identification of the missing lemma,
not a citation for its truth.
