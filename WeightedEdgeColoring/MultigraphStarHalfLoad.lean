import WeightedEdgeColoring.HalfLoad
import WeightedEdgeColoring.MultigraphLocalPolytope

open scoped BigOperators

namespace WeightedEdgeColoring
namespace WeightedMultigraph

variable (G : WeightedMultigraph)

/-- A half-loaded multigraph star lies in its exact local packing polytope. -/
theorem halfLoad_isAverageOfStarFeasibleSets
    {v : G.V} (x : G.StarEdge v → ℝ)
    (hweight : ∀ e : G.StarEdge v, G.weight e.1 ≤ 1 / 2)
    (hx0 : ∀ e, 0 ≤ x e) (hx1 : ∀ e, x e ≤ 1)
    (hload : ∑ e, G.weight e.1 * x e ≤ 1 / 2) :
    G.IsAverageOfStarFeasibleSets v x := by
  apply G.isAverageOfStarFeasibleSets_of_subsetAverage
  exact halfLoad_isAverageOfFeasibleSubsets
    (fun e : G.StarEdge v => G.weight e.1) x
    (fun e => G.weight_pos e.1) hweight hx0 hx1 hload

end WeightedMultigraph
end WeightedEdgeColoring
