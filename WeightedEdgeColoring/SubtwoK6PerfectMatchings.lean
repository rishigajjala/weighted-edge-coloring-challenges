import WeightedEdgeColoring.SubtwoK6MatchingDeficits

/-! The fifteen perfect matchings of the six-vertex complete graph. -/

namespace WeightedEdgeColoring.Subtwo.K6MatchingDeficits

def perfect : Fin 15 → Finset Edge :=
  ![{0,9,14},{0,10,13},{0,11,12},
    {1,6,14},{1,7,13},{1,8,12},
    {2,5,14},{2,7,11},{2,8,10},
    {3,5,13},{3,6,11},{3,8,9},
    {4,5,12},{4,6,10},{4,7,9}]

theorem perfect_isMatching : ∀ i : Fin 15, IsMatching (perfect i) := by
  unfold IsMatching
  decide

end WeightedEdgeColoring.Subtwo.K6MatchingDeficits
