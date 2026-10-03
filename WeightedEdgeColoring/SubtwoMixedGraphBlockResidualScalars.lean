import WeightedEdgeColoring.SubtwoMixedGraphBlockSelectedWord

/-! The block selector's variance-selection error is only a constant
multiple of its sublinear packing deviation, uniformly in graph order. -/

namespace WeightedEdgeColoring

noncomputable section

theorem mixedBlockVarianceSelectionError_le_deviation
    {n B L D k A t δ : ℝ}
    (hn : 0 < n) (ht : 0 < t)
    (hB0 : 0 ≤ B) (hL0 : 0 ≤ L) (hD0 : 0 ≤ D) (hδ0 : 0 ≤ δ)
    (hB : B ≤ D * n) :
    B * ((n + B * L) * (k * A / n) ^ 2 * δ) / (4 * t) ≤
      (D * (1 + D * L) * (k * A) ^ 2 / (4 * t)) * δ := by
  have hBL : B * L ≤ (D * n) * L :=
    mul_le_mul_of_nonneg_right hB hL0
  have hN : n + B * L ≤ (1 + D * L) * n := by
    nlinarith
  have hN0 : 0 ≤ n + B * L := by positivity
  have hDN0 : 0 ≤ (1 + D * L) * n := by positivity
  have hprod : B * (n + B * L) ≤
      (D * n) * ((1 + D * L) * n) :=
    mul_le_mul hB hN hN0 (mul_nonneg hD0 hn.le)
  have hU0 : 0 ≤ (k * A / n) ^ 2 := sq_nonneg _
  have hscale : 0 ≤ δ / (4 * t) := by positivity
  calc
    B * ((n + B * L) * (k * A / n) ^ 2 * δ) / (4 * t) =
        (B * (n + B * L) * (k * A / n) ^ 2) *
          (δ / (4 * t)) := by ring
    _ ≤ ((D * n) * ((1 + D * L) * n) * (k * A / n) ^ 2) *
          (δ / (4 * t)) :=
      mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right hprod hU0) hscale
    _ = (D * (1 + D * L) * (k * A) ^ 2 / (4 * t)) * δ := by
      field_simp [ne_of_gt hn, ne_of_gt ht]

/-- The parameter budget used by the dyadic rounding bridge.  With fixed
block length, its variance-selection error is proportional to `δ/n`; the
sharp product-law variance contributes only `D*S/(4t)`. -/
theorem mixedBlockStarResidualBudget_le
    {n B L D k A S t δ ε : ℝ}
    (hn : 0 < n) (ht : 0 < t)
    (hB0 : 0 ≤ B) (hL0 : 0 ≤ L) (hD0 : 0 ≤ D)
    (hS0 : 0 ≤ S) (hδ0 : 0 ≤ δ) (hε0 : 0 ≤ ε)
    (hB : B ≤ D * n) (hδ : δ ≤ ε * n) :
    t * n +
      B * (S + (n + B * L) * (k * A / n) ^ 2 * δ) / (4 * t) ≤
    (t + D * S / (4 * t) +
      D * (1 + D * L) * (k * A) ^ 2 * ε / (4 * t)) * n := by
  have hfirst : B * S / (4 * t) ≤
      (D * S / (4 * t)) * n := by
    have h := mul_le_mul_of_nonneg_right hB hS0
    have hd := div_le_div_of_nonneg_right h (by positivity : 0 ≤ 4 * t)
    convert hd using 1 <;> ring
  have herr := mixedBlockVarianceSelectionError_le_deviation
    hn ht hB0 hL0 hD0 hδ0 hB (k := k) (A := A)
  have hcoeff : 0 ≤ D * (1 + D * L) * (k * A) ^ 2 / (4 * t) := by
    positivity
  have hsecond :
      (D * (1 + D * L) * (k * A) ^ 2 / (4 * t)) * δ ≤
      (D * (1 + D * L) * (k * A) ^ 2 / (4 * t)) *
        (ε * n) := mul_le_mul_of_nonneg_left hδ hcoeff
  calc
    t * n + B * (S + (n + B * L) * (k * A / n) ^ 2 * δ) /
        (4 * t) =
      t * n + B * S / (4 * t) +
        B * ((n + B * L) * (k * A / n) ^ 2 * δ) /
          (4 * t) := by ring
    _ ≤ t * n + (D * S / (4 * t)) * n +
        (D * (1 + D * L) * (k * A) ^ 2 / (4 * t)) *
          (ε * n) := by linarith
    _ = _ := by ring

end
end WeightedEdgeColoring
