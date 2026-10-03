import WeightedEdgeColoring.SubtwoK6PerfectMatchings
import WeightedEdgeColoring.SubtwoK6PerfectPrices

/-! Every perfect matching of the concrete six-vertex graph occurs in the
fifteen-row list used by the physical price proof. -/

namespace WeightedEdgeColoring.Subtwo.K6MatchingDeficits

private theorem triple_is_listed (a b c : Edge)
    (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c)
    (hm : IsMatching ({a, b, c} : Finset Edge)) :
    ∃ i : Fin 15, ({a, b, c} : Finset Edge) = perfect i := by
  have habd : Disjoint (ends a) (ends b) := by
    apply hm a (by simp) b (by simp) hab
  have hacd : Disjoint (ends a) (ends c) := by
    apply hm a (by simp) c (by simp) hac
  have hbcd : Disjoint (ends b) (ends c) := by
    apply hm b (by simp) c (by simp) hbc
  clear hm
  fin_cases a <;> decide +revert

theorem perfect_matching_is_listed (M : Finset Edge)
    (hM : IsPerfectMatching M) :
    ∃ i : Fin 15, M = perfect i := by
  obtain ⟨a, b, c, hab, hac, hbc, rfl⟩ := Finset.card_eq_three.mp hM.2
  exact triple_is_listed a b c hab hac hbc hM.1

end WeightedEdgeColoring.Subtwo.K6MatchingDeficits
