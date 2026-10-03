import WeightedEdgeColoring.SubtwoOrdinarySevenSixthsQuotient
import WeightedEdgeColoring.SubtwoOrdinaryBridge

/-!
# Discharge of the ordinary quotient-coloring interface
-/

namespace WeightedEdgeColoring.Subtwo

universe u

theorem quotientOrdinaryColoring_proved : QuotientOrdinaryColoring.{u} := by
  intro η hη
  obtain ⟨N, hN⟩ := WeightedEdgeColoring.exists_ordinaryColoring_subtwo_quotient.{u} η hη
  refine ⟨N, ?_⟩
  intro G F n hn hdegree hodd
  have hdegree' : ∀ v, (G.degreeOn F v : ℝ) ≤
      (1691031 / 1000000 : ℝ) * n := by
    intro v
    simpa [ordinaryDegreeCoefficient] using hdegree v
  have hodd' : G.OddSetDensityAtMost F
      ((1999 / 1000 : ℝ) * n) := by
    simpa [ordinaryTargetCoefficient] using hodd
  obtain ⟨q, hq, hqBound, color, hproper⟩ :=
    hN G F n hn hdegree' hodd'
  exact ⟨q, hq,
    by simpa [ordinaryTargetCoefficient] using hqBound,
    color, hproper⟩

end WeightedEdgeColoring.Subtwo
