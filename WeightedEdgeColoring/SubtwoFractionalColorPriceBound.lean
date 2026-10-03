import WeightedEdgeColoring.SubtwoGraphPalette
import WeightedEdgeColoring.SubtwoGraphPatternCopies
import WeightedEdgeColoring.SubtwoFractionalStarDemand

/-! A fractional weighted coloring is a valid witness for every nonnegative
color-price dual vector. -/

open scoped BigOperators

namespace WeightedEdgeColoring.WeightedMultigraph

universe u
variable (G : WeightedMultigraph.{u})

theorem SubtwoFractionalDemandColoring.price_le_colorMax
    {demand : G.E → ℝ} (C : G.SubtwoFractionalDemandColoring demand)
    (price : G.E → ℝ) :
    (∑ e : G.E, price e * demand e) ≤
      C.cost * G.subtwoColorPriceMax price := by
  classical
  have hp (p : C.P) :
      (∑ e : G.E, price e * (C.pattern p e : ℝ)) ≤
        G.subtwoColorPriceMax price := by
    let pat : G.SubtwoWeightedPattern := ⟨C.pattern p, C.feasible p⟩
    exact Subtwo.patternPrice_le_paletteMaxScore
      G.subtwoReservedColorPattern price none pat
  calc
    _ = ∑ e : G.E, ∑ p : C.P,
          C.mass p * (price e * (C.pattern p e : ℝ)) := by
      apply Finset.sum_congr rfl
      intro e _
      rw [← C.covers e, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro p _
      ring
    _ = ∑ p : C.P, ∑ e : G.E,
          C.mass p * (price e * (C.pattern p e : ℝ)) := Finset.sum_comm
    _ = ∑ p : C.P, C.mass p *
          (∑ e : G.E, price e * (C.pattern p e : ℝ)) := by
      apply Finset.sum_congr rfl
      intro p _
      rw [Finset.mul_sum]
    _ ≤ ∑ p : C.P, C.mass p * G.subtwoColorPriceMax price := by
      exact Finset.sum_le_sum (fun p _ ↦ mul_le_mul_of_nonneg_left (hp p) (C.mass_nonneg p))
    _ = _ := by simp [SubtwoFractionalDemandColoring.cost, Finset.sum_mul]

theorem triangleLocalBins_price_bound
    (hcard : Fintype.card G.V = 3)
    (demand price : G.E → ℝ) (B : G.SubtwoLocalFractionalBins demand)
    (hp : ∀ e, 0 ≤ price e)
    (htotal : ∀ v, (∑ p, B.mass v p) ≤ 1) :
    (∑ e : G.E, price e * demand e) ≤
      (3/2:ℝ) * G.subtwoColorPriceMax price := by
  obtain ⟨C, hcost⟩ :=
    G.exists_subtwoFractionalDemandColoring_triangle demand B 1 hcard htotal
  have h := C.price_le_colorMax G price
  exact h.trans (mul_le_mul_of_nonneg_right (by simpa using hcost)
    (G.subtwoColorPriceMax_nonneg price hp))

end WeightedEdgeColoring.WeightedMultigraph
