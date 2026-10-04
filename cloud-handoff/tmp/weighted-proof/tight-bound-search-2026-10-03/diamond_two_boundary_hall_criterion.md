# Exact two-boundary color permutation criterion for a diamond

**Interim structural lemma, not a weighted-edge-coloring bound.** Consider two internally disjoint colored arms between a common source and sink. Ignore for the moment per-color multiplicities above one on each boundary bundle, and record for each color on an arm a bit at the source and at the sink: `00`, `10`, `01`, `11`. Let `a_xy` and `b_xy` be the numbers of these four states on arms A and B, respectively, each totaling the same palette size `M`.

One may permute the complete `M`-color list of arm B while preserving its internal coloring. The two arms can then be glued so that they never both occupy the source in one color and never both occupy the sink in one color **if and only if**

    a10+a11 + b10+b11 <= M,      (source marginals)
    a01+a11 + b01+b11 <= M,      (sink marginals)
    a11 <= b00,                  (A through-colors need B empty)
    b11 <= a00.                  (B through-colors need A empty)

Proof: form the bipartite compatibility graph on color states, allowing a pair exactly when no coordinate is one in both states. State `11` has only neighbor `00`; state `10` has neighbors `00,01`; state `01` has neighbors `00,10`; state `00` has all four neighbors. Hall subsets reduce to: `11` alone, `10+11`, `01+11`, and all three nonzero states. These are precisely the four displayed inequalities (the last one after complementation). Since all colors have a state and both lists have size `M`, an integral perfect matching gives the needed permutation.

The cross conditions are genuinely additional to source/sink marginal feasibility. For example, take A with half its colors `11` and half `00`, and B with half `10` and half `01`. Every source and sink marginal sum is exactly `M`, but `a11=M/2>b00=0`, so no permutation glues them. This is the precise abstract identity-versus-complement phase frustration sought on a bipartite diamond.

In weighted edge coloring, each boundary bit may need to be replaced by an integer packet count, and the source/sink may permit compatible packets from the two arms in one color. The lemma is therefore an exact criterion only for the stated binary incompatible-boundary-state abstraction. A physical lower bound above `4/3` requires constructing arm laws that force these conflicting joint states while their local bin maximum remains sufficiently small. The targeted `.4` to `.3` full/partial guard-matching diamond diagnostic in `graded_diamond_full_matching_probe.py` found no such gain (maximum sampled repeatable-count ratio `7/6`); that numerical observation is not a theorem over all demands or weights.
