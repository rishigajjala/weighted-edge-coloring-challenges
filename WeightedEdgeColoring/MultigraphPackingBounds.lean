import WeightedEdgeColoring.WeightedMultigraph

namespace WeightedEdgeColoring
namespace WeightedMultigraph

variable (G : WeightedMultigraph)

/-- A uniform local packing bounds the total weight at every vertex. -/
theorem starWeight_le_of_locallyPacksInto {n : ℕ}
    (h : G.LocallyPacksInto n) (v : G.V) : G.starWeight v ≤ n :=
  G.starWeight_le_of_packsStarInto (h v)

end WeightedMultigraph
end WeightedEdgeColoring
