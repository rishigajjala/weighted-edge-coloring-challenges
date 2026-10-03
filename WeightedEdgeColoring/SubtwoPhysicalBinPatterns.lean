import WeightedEdgeColoring.SubtwoPhysicalHeavyClasses
import WeightedEdgeColoring.SubtwoGraphPatternCopies

/-!
# Priced patterns made from the original star bins

Restricting one actual star bin to a set of physical edges gives a genuine
weighted graph color. Its load is the projection load used in the profile
rows, and summing its price over all bins recovers the physical edge prices.
-/

open scoped BigOperators

namespace WeightedEdgeColoring.WeightedMultigraph
noncomputable section
attribute [local instance] Classical.propDecidable
universe u
variable (G : WeightedMultigraph.{u})

def subtwoStarBinMultiplicity (F : Finset G.E) {v : G.V} {n : ℕ}
    (bin : G.StarEdge v → Fin n) (j : Fin n) (e : G.E) : ℕ :=
  if he : G.Inc v e then if e ∈ F ∧ bin ⟨e, he⟩ = j then 1 else 0 else 0

theorem subtwoStarBinMultiplicity_load (F : Finset G.E) {v : G.V} {n : ℕ}
    (bin : G.StarEdge v → Fin n) (j : Fin n) :
    (∑ e : G.E, (G.subtwoStarBinMultiplicity F bin j e : ℝ) * G.weight e) =
      G.subtwoStarProjectionLoad F bin j := by
  classical
  calc
    _ = ∑ e : G.E, if e ∈ F then G.subtwoStarBinEdgeWeight bin j e else 0 := by
      apply Finset.sum_congr rfl
      intro e he
      by_cases hf : e ∈ F <;> by_cases hi : G.Inc v e <;>
        simp [subtwoStarBinMultiplicity, subtwoStarBinEdgeWeight, hf, hi, ite_mul]
    _ = _ := by
      rw [← Finset.sum_filter]
      simp [subtwoStarProjectionLoad]

def subtwoStarBinPattern (F : Finset G.E) {v : G.V} {n : ℕ}
    (bin : G.StarEdge v → Fin n) (hbin : ∀ j, G.starBinLoad bin j ≤ 1)
    (j : Fin n) : G.SubtwoWeightedPattern :=
  SubtwoWeightedPattern.ofTotalLoad G (G.subtwoStarBinMultiplicity F bin j) (by
    rw [G.subtwoStarBinMultiplicity_load]
    exact (G.subtwoStarProjectionLoad_le_star F bin j).trans (hbin j))

def subtwoStarProjectionPrice (F : Finset G.E) {v : G.V} {n : ℕ}
    (bin : G.StarEdge v → Fin n) (j : Fin n) (price : G.E → ℝ) : ℝ :=
  ∑ e : G.E, price e * (G.subtwoStarBinMultiplicity F bin j e : ℝ)

theorem subtwoStarProjectionPrice_nonneg (F : Finset G.E) {v : G.V} {n : ℕ}
    (bin : G.StarEdge v → Fin n) (j : Fin n) (price : G.E → ℝ)
    (hp : ∀ e, 0 ≤ price e) : 0 ≤ G.subtwoStarProjectionPrice F bin j price :=
  Finset.sum_nonneg fun e _ => mul_nonneg (hp e) (Nat.cast_nonneg _)

theorem subtwoStarProjectionPrice_eq (F : Finset G.E) {v : G.V} {n : ℕ}
    (bin : G.StarEdge v → Fin n) (j : Fin n) (price : G.E → ℝ) :
    G.subtwoStarProjectionPrice F bin j price =
      ∑ e ∈ F, if he : G.Inc v e then
        (if bin ⟨e, he⟩ = j then price e else 0) else 0 := by
  classical
  calc
    _ = ∑ e : G.E, if e ∈ F then
        (if he : G.Inc v e then (if bin ⟨e, he⟩ = j then price e else 0) else 0) else 0 := by
      apply Finset.sum_congr rfl
      intro e he
      by_cases hf : e ∈ F <;> by_cases hi : G.Inc v e <;>
        simp [subtwoStarBinMultiplicity, hf, hi, mul_ite]
    _ = _ := by rw [← Finset.sum_filter]; simp

theorem subtwoStarBinPattern_support (F : Finset G.E) (S : Finset G.V)
    (hF : ∀ e ∈ F, G.fst e ∈ S ∧ G.snd e ∈ S)
    {v : G.V} {n : ℕ} (bin : G.StarEdge v → Fin n)
    (hbin : ∀ j, G.starBinLoad bin j ≤ 1) (j : Fin n) :
    ∀ e, (G.subtwoStarBinPattern F bin hbin j).val e ≠ 0 →
      G.fst e ∈ S ∧ G.snd e ∈ S := by
  intro e he
  apply hF e
  by_contra hf
  apply he
  change G.subtwoStarBinMultiplicity F bin j e = 0
  simp [subtwoStarBinMultiplicity, hf]

theorem subtwoStarProjectionPrice_le_harmonic
    (F : Finset G.E) (S : Finset G.V)
    (hF : ∀ e ∈ F, G.fst e ∈ S ∧ G.snd e ∈ S)
    {v : G.V} {n : ℕ} (bin : G.StarEdge v → Fin n)
    (hbin : ∀ j, G.starBinLoad bin j ≤ 1) (j : Fin n) (price : G.E → ℝ) :
    G.subtwoStarProjectionPrice F bin j price ≤
      G.subtwoSupportedPriceMax S price * harmonicCharge (G.subtwoStarProjectionLoad F bin j) := by
  have h := G.subtwo_pattern_price_le_harmonic_charge
    (G.subtwoStarBinPattern F bin hbin j) S
    (G.subtwoStarBinPattern_support F S hF bin hbin j)
    (by
      change (∑ e, (G.subtwoStarBinMultiplicity F bin j e : ℝ) * G.weight e) ≤ 1
      rw [G.subtwoStarBinMultiplicity_load]
      exact (G.subtwoStarProjectionLoad_le_star F bin j).trans (hbin j)) price
  change G.subtwoStarProjectionPrice F bin j price ≤
    G.subtwoSupportedPriceMax S price * harmonicCharge
      (∑ e, (G.subtwoStarBinMultiplicity F bin j e : ℝ) * G.weight e) at h
  rwa [G.subtwoStarBinMultiplicity_load] at h

theorem subtwoStarProjectionPrice_le_max (F : Finset G.E) {v : G.V} {n : ℕ}
    (bin : G.StarEdge v → Fin n) (hbin : ∀ j, G.starBinLoad bin j ≤ 1)
    (j : Fin n) (price : G.E → ℝ) :
    G.subtwoStarProjectionPrice F bin j price ≤ G.subtwoColorPriceMax price :=
  Subtwo.patternPrice_le_paletteMaxScore G.subtwoReservedColorPattern price none
    (G.subtwoStarBinPattern F bin hbin j)

theorem sum_subtwoStarProjectionPrice (F : Finset G.E) {v : G.V} {n : ℕ}
    (bin : G.StarEdge v → Fin n) (price : G.E → ℝ) :
    (∑ j : Fin n, G.subtwoStarProjectionPrice F bin j price) =
      ∑ e ∈ F, if G.Inc v e then price e else 0 := by
  classical
  unfold subtwoStarProjectionPrice
  rw [Finset.sum_comm]
  calc
    _ = ∑ e : G.E, if e ∈ F then (if G.Inc v e then price e else 0) else 0 := by
      apply Finset.sum_congr rfl
      intro e he
      by_cases hf : e ∈ F <;> by_cases hi : G.Inc v e <;>
        simp [subtwoStarBinMultiplicity, hf, hi, mul_ite]
    _ = _ := by rw [← Finset.sum_filter]; simp

/-- The actual total price on one star is paid by its number of bins. -/
theorem subtwo_star_price_le_bins_mul_max (F : Finset G.E) {v : G.V} {n : ℕ}
    (bin : G.StarEdge v → Fin n) (hbin : ∀ j, G.starBinLoad bin j ≤ 1)
    (price : G.E → ℝ) :
    (∑ e ∈ F, if G.Inc v e then price e else 0) ≤ (n : ℝ) * G.subtwoColorPriceMax price := by
  rw [← G.sum_subtwoStarProjectionPrice F bin price]
  calc
    _ ≤ ∑ _j : Fin n, G.subtwoColorPriceMax price :=
      Finset.sum_le_sum fun j hj => G.subtwoStarProjectionPrice_le_max F bin hbin j price
    _ = _ := by simp

end
end WeightedEdgeColoring.WeightedMultigraph
