# Polar-vertex gap search checkpoint

Stopped on parent request to return to repository cleanup. No
repository or manuscript files were edited.

`bipartite_rank_two_polar_gap.py` enumerates all exact integer global
patterns for a fixed small bipartite rank-two weight template, keeps
coordinatewise maximal patterns, enumerates vertices of the bounded
polar `q>=0, Pq<=1` with Qhull, and maximizes `q·x` over the exact
local rank-two configuration polytope with HiGHS at every polar
vertex. Since the local support function is convex, its maximum over
the polar occurs at a polar vertex, so this computes the full
configuration gap for that weight template up to numerical precision.
The template choice is sampled; no universal bound follows.

Completed sweeps in `bipartite_rank_two_polar_k33.log` and
`bipartite_rank_two_polar_c4double.log` tested respectively 300
`K3,3` and 500 doubled-`C4` weight templates with no Qhull failure.
Both sampled maxima were exactly numerical `5/4`.

The ten-type guarded-path-plus-chord sweep was interrupted after its
case-200 progress report. Its best recorded gap was `1.2875=103/80`
for weights `[49,47,44,35,51,53,56,65,75,60]`. The maximizing polar
profit has zero chord coordinate and equal `1/5` profit on the nine
tree types, so this candidate provides no cycle-based improvement.
The partial log is `bipartite_rank_two_polar_pathchord.log`.

These computations found no `>4/3` bipartite obstruction. A numerical
candidate above `4/3`, if one is later found, must be audited with
exact rational local and global witnesses before claiming a theorem.
