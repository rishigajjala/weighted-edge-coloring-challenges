import WeightedEdgeColoring.BoundedMultiplicityLargeEdgeRestriction
import WeightedEdgeColoring.BoundedMultiplicityEndpointGroups

namespace WeightedEdgeColoring

open scoped BigOperators

noncomputable section

namespace WeightedMultigraph

universe u v w

variable (G : WeightedMultigraph.{u})
  {Slot : Type v} {Option : Type w}
  [Fintype Slot] [Fintype Option]
  [DecidableEq Slot] [DecidableEq Option]
  (H : RankThreeOptionSystem G.E Slot Option)

/-- The large indexed edges not covered by an option set. -/
def uncoveredLargeEdges (beta : ℝ) (M : Finset Option) : Finset G.E :=
  (G.largeEdgeJobs beta).filter fun e ↦ ¬ H.Covers M e

@[simp] theorem mem_uncoveredLargeEdges
    {beta : ℝ} {M : Finset Option} {e : G.E} :
    e ∈ G.uncoveredLargeEdges H beta M ↔
      beta ≤ G.weight e ∧ ¬ H.Covers M e := by
  simp [uncoveredLargeEdges]

/-- Star weight of the large indexed edges not covered by `M`. -/
def uncoveredLargeStarWeight
    (beta : ℝ) (M : Finset Option) (vtx : G.V) : ℝ :=
  ∑ e ∈ G.activeStarEdgeSet (G.uncoveredLargeEdges H beta M) vtx,
    G.weight e

end WeightedMultigraph

end


end WeightedEdgeColoring
