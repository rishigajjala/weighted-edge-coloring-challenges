import WeightedEdgeColoring.SubtwoSelectorConditioning

/-!
# Clipping a selected option mass

A lower bound on raw option mass does not control the residual after clipping:
surplus on one edge can mask a deficit on another.  This deterministic lemma
records the missing quadratic term.  It applies to any finite edge family and
does not depend on the construction of the selected word.
-/

namespace WeightedEdgeColoring

open scoped BigOperators

noncomputable section

theorem clipped_residual_le_mean_deficit_add_variance
    (mass mean t : ℝ) (ht : 0 < t) :
    1 - min 1 mass ≤ max 0 (1 - mean) + t +
      (mass - mean) ^ 2 / (4 * t) := by
  have ht4 : 0 < 4 * t := by positivity
  have hquad : mean - mass - t ≤ (mass - mean) ^ 2 / (4 * t) := by
    apply (le_div_iff₀ ht4).2
    nlinarith [sq_nonneg (mass - mean + 2 * t)]
  have hsq : 0 ≤ (mass - mean) ^ 2 / (4 * t) :=
    div_nonneg (sq_nonneg _) ht4.le
  rcases le_total mass 1 with hm | hm
  · rw [min_eq_right hm]
    rcases le_total mean 1 with hmu | hmu
    · rw [max_eq_right (by linarith : 0 ≤ 1 - mean)]
      linarith
    · rw [max_eq_left (by linarith : 1 - mean ≤ 0)]
      linarith
  · rw [min_eq_left hm]
    have hmax : 0 ≤ max 0 (1 - mean) := le_max_left _ _
    linarith

theorem sum_clipped_residual_le_mean_deficit_add_variance
    {E : Type*} [Fintype E]
    (weight mass mean : E → ℝ) (t : ℝ) (ht : 0 < t)
    (hw : ∀ e, 0 ≤ weight e) :
    (∑ e, weight e * (1 - min 1 (mass e))) ≤
      (∑ e, weight e * max 0 (1 - mean e)) +
      t * (∑ e, weight e) +
      (∑ e, weight e * (mass e - mean e) ^ 2) / (4 * t) := by
  have ht4 : 0 < 4 * t := by positivity
  calc
    (∑ e, weight e * (1 - min 1 (mass e))) ≤
        ∑ e, weight e * (max 0 (1 - mean e) + t +
          (mass e - mean e) ^ 2 / (4 * t)) := by
      apply Finset.sum_le_sum
      intro e _
      exact mul_le_mul_of_nonneg_left
        (clipped_residual_le_mean_deficit_add_variance
          (mass e) (mean e) t ht) (hw e)
    _ = (∑ e, weight e * max 0 (1 - mean e)) +
        t * (∑ e, weight e) +
        (∑ e, weight e * (mass e - mean e) ^ 2) / (4 * t) := by
      calc
        (∑ e, weight e * (max 0 (1 - mean e) + t +
          (mass e - mean e) ^ 2 / (4 * t))) =
          ∑ e, (weight e * max 0 (1 - mean e) +
            t * weight e +
            (weight e * (mass e - mean e) ^ 2) / (4 * t)) := by
          apply Finset.sum_congr rfl
          intro e _
          ring
        _ = (∑ e, weight e * max 0 (1 - mean e)) +
            t * (∑ e, weight e) +
            (∑ e, weight e * (mass e - mean e) ^ 2) / (4 * t) := by
          rw [Finset.sum_add_distrib, Finset.sum_add_distrib,
            ← Finset.mul_sum, ← Finset.sum_div]

end
end WeightedEdgeColoring
