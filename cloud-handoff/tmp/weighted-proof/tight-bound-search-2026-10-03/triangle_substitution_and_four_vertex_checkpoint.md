# Triangle substitution checkpoint (2026-10-03)

This note concerns one-color configuration hulls, not a uniform integer
coloring theorem. The established general lower bound remains `3/2`;
none of the tested substitutions exceeds it. All numerical polar claims
below are floating-point diagnostics and are not universal proofs.

## Exact three-vertex barrier

Let `P` be the intersection of exact local one-bin hulls for any loopless
weighted multigraph supported on three vertices `a,b,c`, with arbitrary
positive edge weights at most one and arbitrary parallel types. Let `Q`
be the convex hull of globally feasible one-bin count patterns. Then

    (2/3) P subset Q.

For `x in P`, choose each vertex as a center with probability `1/3`.
Conditional on center `v`, sample any local feasible integer pattern
whose mean is the incident restriction `x|delta(v)`, and set all other
edge counts to zero. The sampled star is globally feasible: the center
fits by construction, and each other vertex sees a subcollection of
the center's feasible pattern. Every edge has two possible centers, so
its resulting mean is `(2/3)x_e`. The unit-weight triangle attains the
ratio `3/2`. Consequently, no mixture of ranks, parallel types, or
edge substitutions that remain on three vertices can improve this
lower bound.

## Tested odd-cycle substitution

The five-vertex `a-u-v-b-c-a` model has heavy `a-u` of weight `w>1/2`
and `v-b` of weight one, with divisible fluid on `u-v`, `a-c`, `b-c`.
The fluid edge `u-v` favors correlated heavy-free states; the pair via
`c` competes for its central capacity. The exact heavy-state/fluid LP
and full local vertex enumeration in
`triangle_blocker_substitution_fluid_gauge.py` give a maximum gap of
`5/4` at every checked `w=0.500001,0.51,0.6,0.75,0.9,1`. There are 25
local vertices for `w<1` and 12 at `w=1`. This is not a continuous-in-`w`
theorem. It shows that one natural attempt to replace a triangle edge
with a two-blocker path dilutes, rather than compounds, the loss.

## Targeted four-vertex full-profit diagnostics

`general_k4_mixed_rank_polar.py` enumerates every global count pattern,
all local knapsack patterns, every nonnegative-profit polar vertex, and
the exact local LP at that profit for six-type `K4` templates. It checked:

    (100,100,100; 51,34,26)  gap 3/2
    (60,60,60; 40,34,26)    gap 3/2
    (60,60,60; 40,40,40)    gap 3/2
    (51,51,51; 34,34,34)    gap 3/2
    (60,51,40; 40,34,26)    gap 5/4
    (51,40,34; 34,26,26)    gap 11/9
    (60,40,26; 40,26,20)    gap 6/5
    (51,34,26; 51,34,26)    gap 5/4
    (60,60,40; 40,40,26)    gap 5/4
    (100,60,60; 40,40,26)   gap 3/2

The first triple names the three edges among vertices `0,1,2`; the
second names their spokes to vertex `3`. Every displayed `3/2` optimum
has a profit support reducible to an ordinary triangle or the known
single-heavy plus two-fluid triangle. Mixed-rank spokes did not amplify
the gap on these templates.

`general_triangle_two_type_polar.py` checked doubled edge types on each
side of a triangle. It returned gaps `3/2` for `(60,40)` repeated and
`(60,26)` repeated, `9/8` for `(40,26)` repeated, and `4/3` for the
heterogeneous sides `(60,40),(51,34),(40,26)`. The exact three-vertex
lemma above already proves the universal upper bound for that topology;
the numerical checks are merely diagnostics of particular templates.

The live route requires at least four essential vertices and a
boundary-response gadget whose local demand cannot be realized by
sampling one star. In particular, adding ranks on the same triangle or
serially subdividing one side has no observed amplification.

## Targeted finite falsification of a `3/2` small-support hypothesis

The K4 script was applied to **every** assignment of the alphabet
`{100,60,51,40,34,26}/100` to its six edge types, modulo the 24 vertex
automorphisms. All 2,451 inequivalent templates had full nonnegative
profit-polar gap at most `3/2`, with equality already from a unit-weight
triangle. The four-weight subalphabet `{100,60,40,26}/100` covered 276
orbits, also max `3/2`. This is finite-alphabet evidence only. See
`general_k4_targeted_hypothesis_sweep.py`.

A second topology has two triangles `0-1-2-0` and `0-3-4-0` sharing
their center `0`. `general_bowtie_mixed_polar.py` and
`general_bowtie_hypothesis_sweep.py` checked all 8,001 inequivalent
six-weight-alphabet assignments (eight graph automorphisms), again full
profit-polar gap at most `3/2`; the four-weight subalphabet covered 820
orbits. The earlier `triangle-block-forest-three-halves.md` packet
argument was retracted, so this computational observation does not
establish any block-gluing theorem.

An essential five-vertex theta graph, the five-cycle plus a chord
forming one triangle and one four-cycle, was also checked on six
targeted heterogeneous templates using
`general_c5_chord_mixed_polar.py`. Gaps ranged `5/4` to `4/3`; none
exceeded `3/2`. These are diagnostics, not a search of all thresholds.

One tempting stronger subdivision claim is false: a single-type
weighted five-cycle need not have gap at most the ordinary matching
value `5/4`. The exact finite template with edge weights
`(26,40,100,26,60)/100` in cyclic order, profit `q=(2,2,3,1,4)`,
and local point `x=(12/7,8/7,3/7,12/7,9/14)` has local profit
`79/7`, whereas direct enumeration of all feasible one-color count
patterns gives global maximum `9`. Hence its configuration ratio is
`79/63 > 5/4`. Exact local decompositions into feasible count pairs
at cycle vertices `0,...,4` are respectively:

    v0: (1,1) with 9/14, (3,0) with 5/14
    v1: (0,2) with 1/7,  (2,1) with 6/7
    v2: (0,1) with 3/7,  (2,0) with 4/7
    v3: (0,3) with 4/7,  (1,0) with 3/7
    v4: (1,1) with 9/14, (3,0) with 5/14

For each vertex the pair coordinates follow the incident cycle-edge
indices in ascending order. The six-weight alphabet sweep checked all
888 inequivalent five-cycle assignments and found maximum `79/63`.
This result is far weaker than the established general `3/2` lower
bound; its role here is only to rule out a naive assertion that serial
subdivision has exactly the ordinary odd-cycle loss.

## Five-vertex nonlocal parity diagnostic

`general_k5_cycle_chords_polar.py` orders K5 edges as a five-cycle
followed by its five complementary chords. Structured templates with
graded heavy cycle weights and medium/rank-three chords, including
`(60,64,68,72,76;40,36,32,28,24)` and
`(60,64,68,72,76;40,34,26,24,20)`, yielded full-profit gaps `3/2`
and `10/7`, respectively. In the `3/2` cases, a maximizing profit
direction is supported on a triangle embedded in K5.

To challenge the sharper hypothesis that K5 could create a gap above
`3/2`, `general_k5_targeted_hypothesis_sweep.py` checked **all 792**
inequivalent assignments of weights from `{100,60,40}/100` to K5's
ten edges. For every template it enumerated all repeatable global
count patterns, all nonnegative-profit polar vertices, and optimized
the exact local knapsack LP. The maximum observed gap was `3/2`.
This is a finite-threshold falsification attempt, not an unrestricted
five-vertex upper bound.

The larger K5 interface experiments were harder. A 12-type K5 with
parallel rank-three types on two chords made the full polar enumeration
CPU-bound, so it was stopped and replaced with
`general_k5_parallel_chords_milp.py`. For the graded weights
`(60,64,68,72,76;40,36,32,28,24;26,26)`, exhaustive separation over
every integer profit vector with coordinates at most 12 found no
`q·x>(3/2) max_pattern q·z` violation. The mixed 15-type version
`general_k5_parallel_cycle_heavy_milp.py`, with two heterogeneous
heavy types on each cycle side and five graded chords, likewise found
none for profits at most six. With coordinate bound 12 its reported
positive objective was only about `10^-5`, coinciding with solver
feasibility tolerance; it is not treated as a witness. These bounded
profit tests do not cover arbitrary real profit directions.

## A failed cut-vertex law shortcut

Matching edge means is insufficient for a triangle-block gluing
proof. In a triangle `c-a-b-c`, give `ca,cb` weight `2/5` and base
`ab` weight one. The local point with `x_ca=x_cb=3/4`, `x_ab=1/4` is
globally feasible: use both spokes together in `3/4` of colors and the
base in `1/4`. After scaling by `2/3`, however, prescribing the center
`c` to choose exactly one spoke in each color, equally often, gives
the correct scaled spoke means `1/2` each yet makes every color
incompatible with the unit base. Thus no global law with that prescribed
center distribution can realize scaled base mean `1/6`. A suitable
center law does exist (both spokes together with probability `1/2`).
Any articulation-gluing proof must choose coherent *joint* center
states rather than accept arbitrary center laws with correct means.
