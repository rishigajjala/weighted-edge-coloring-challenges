# Finite labels for bounded-radius neighborhoods in a sparse random graph

3 October 2026. Research candidate under independent audit. This auxiliary
statement is being used to investigate a physical-coloring theorem in the
matching-heavy regime; it is not an unrestricted weighted-coloring result.

## Statement

Let J be a finite random simple graph whose distinct edge indicators are
independent. Let T be a symmetric nonnegative matrix, with zero diagonal,
such that Pr(uv in J) <= T_uv and every row sum is at most K. Fix an integer
r >= 0 and delta > 0. There is a labeling of the vertices with a finite
number of labels depending only on K,r,delta such that, for every vertex v,

    Pr[the radius-r ball of v in J has two distinct vertices
       with the same label] <= delta.

The same conclusion holds for any random subgraph obtained by deleting
edges from J, even when deletion decisions are dependent. Parallel sampled
bundles may be replaced by their superedge indicator: indicators belonging
to different unordered endpoint pairs remain independent, and the
superedge probability is at most the sum of the bundle probabilities.

## The concentration input

Use Proposition `prop:HS` in the current manuscript. Independent finite
choices Z_i and nonnegative additive rows F_t=sum_i f_ti(Z_i), with each
coefficient in [0,1], admit a simultaneous choice with

    F_t <= E F_t + O(sqrt(R log(C+2)) + log(C+2)),

where R=max_t E F_t, D=max_(i,z) sum_t f_ti(z), and C=max(2,R,D).
The implicit constant is absolute. No count of rows or sources occurs.

## A deterministic weighted-neighborhood labeling

Put W=I+T+...+T^r and S=sum_(ell=0)^r K^ell. Both row and column sums of W
are at most S, since W is symmetric. Choose a small desired weak load eta,
then an integer Q with S/Q <= eta/4, and then gamma>0 sufficiently small.

Call A a strong neighbor of j when W_jA>gamma. Each j has at most S/gamma
such neighbors. On distinct vertices form the undirected strong graph and
properly color its square. Include j itself when considering its closed
strong neighborhood. Thus any two distinct strong neighbors of any j
have distinct base labels. The number of base labels is bounded in terms
of S/gamma only.

Give every vertex A an additional sublabel Z_A in {1,...,Q}. Initially
choose these independently and uniformly. For every j, base label b and
sublabel s, form the weak-load row

    L_(j,b,s) = sum_(A: W_jA<=gamma, base(A)=b)
                    W_jA * 1[Z_A=s].

Its expectation is at most S/Q. Divide coefficients by gamma before
applying HS. The scaled row expectation is at most S/(Q gamma). For one
source A and one choice of its sublabel, its total contribution over ALL
rows is at most (sum_j W_jA)/gamma <= S/gamma: for each j it contributes
to only the row with its own base label and chosen sublabel. In particular,
this bound has no factor for the number of base labels or Q.

The resulting simultaneous choice obeys

    L_(j,b,s) <= S/Q
      + O(sqrt((gamma S/Q) log(2+S/gamma))
           + gamma log(2+S/gamma)) <= eta.

The last inequality follows by choosing gamma sufficiently small AFTER Q.
Only after gamma is fixed is the strong-square base coloring formed; its
number of colors does not enter the preceding HS bounds.

Use (base label, sublabel) as the final label. For each j let

    C_j = sum_(A != B, label(A)=label(B)) W_jA W_jB.

For a fixed final label let s be its total strong mass and w its total
weak mass. There is at most one strong vertex, and w<=eta. Its contribution
to C_j is at most 2sw+w^2, since diagonal terms are omitted. Summing over
labels therefore gives

    C_j <= 2 eta * (total strong mass) + eta * (total weak mass)
        <= 2 eta S.

## Rooted witness trees

If the radius-r ball of v contains distinct same-label vertices A,B,
choose a breadth-first tree of that ball. The union of its v--A and
v--B paths has a branch vertex j and three pairwise edge-disjoint arms:
v--j, j--A, j--B, each of length at most r. An arm can have length zero.
For a fixed such tree, independence bounds its occurrence probability by
the product of T over its distinct edges.

Union-bound over these trees. Dropping simplicity and disjointness in the
SUM of their product weights only adds nonnegative terms. The sum over
v--j walks of length at most r is W_vj, and the other two arm sums are
bounded by W_jA and W_jB. Therefore

    Pr[bad radius-r ball at v]
        <= sum_j W_vj C_j
        <= 2 eta S^2.

Take eta <= delta/(2S^2). This proves the proposed finite-label statement,
subject to verification of the cited HS input and the interfaces above.
The counting does not multiply probabilities for shared path edges: the
initial witness is a TREE with disjoint arms. Walks are introduced only
after summing those valid independent products.

## Intended use and its limit

Sparsify normalized tiny target y by keeping a bundle of size y_e>=epsilon
deterministically and sampling each smaller bundle with probability
y_e/epsilon, giving it temporary target epsilon. Prune excessive-load
vertices and scale; then a retained graph has bounded degree, while the
unpruned superedge matrix has row sum at most 2/epsilon after heavy pairs
are contracted. The lemma controls bad local balls at every root.

It is essential to average sampled-graph policies WITHIN each physical
color. Sampling just one graph per color can put target epsilon on an edge
whose original y_e is arbitrarily smaller. Averaging restores the cap
12 E[y_e^S] <= 12 y_e.

The lemma gives an unconditional root probability, not a bound conditional
on a rare probe edge being sampled. That is sufficient for total lost
stock at a vertex: sampled total target there is at most one, so target
lost by deleting every local policy touching a bad root ball has expectation
at most the bad-ball probability (times the fixed policy cap factor).
This still needs to be combined carefully with the capped localized-flow
theorem, real-residual augmentation, exact heavy stocks, and whole-edge
rounding before it yields a coloring theorem.

## Independent checks received

The lower-bound agent independently checked the full argument, including
zero-length witness arms, the order Q then gamma then base coloring, and
the absence of a base-label factor in the HS source-column bound. It also
checked the underlying primary source, Harris--Srinivasan, Theorem 4.7 in
https://arxiv.org/html/1406.5943v5 . That theorem permits the per-option
column-sum formulation used by the manuscript proposition. The physical
rounding agent independently checked the unconditional-root versus
rare-edge-conditioned distinction and agrees that root probabilities
suffice for bounding total discarded target at each vertex. The whole
physical-coloring application remains under audit.
