import WeightedEdgeColoring.WeightedMomentGraphExpansion

/-!
# From mixed coordinates to the graph squared-error estimate

This is the deterministic second half of the pairing schedule.  Uniform
coordinate estimates for `z`, `d`, and ordered `Z` imply the two overlap
moment bounds, with exactly the constants consumed by
`WeightedMomentErrorBound`.
-/

namespace WeightedEdgeColoring
namespace WeightedMultigraph

open scoped BigOperators
open WeightedEdgeColoring.WeightedMomentStatistics
open WeightedEdgeColoring.WeightedMomentErrorBound

noncomputable section

universe u

variable (G : WeightedMultigraph.{u})

theorem sum_paletteIndicator_mul_bound {q : ℕ}
    (S : Finset (Fin q)) (x : Fin q → ℝ) {mu eta : ℝ}
    (hx : ∀ c, x c ≤ mu + eta) :
    (∑ c : Fin q, paletteIndicator S c * x c) ≤
      S.card * (mu + eta) := by
  calc
    (∑ c : Fin q, paletteIndicator S c * x c) ≤
        ∑ c : Fin q, paletteIndicator S c * (mu + eta) := by
      apply Finset.sum_le_sum
      intro c _hc
      exact mul_le_mul_of_nonneg_left (hx c) (by
        unfold paletteIndicator
        split <;> norm_num)
    _ = S.card * (mu + eta) := by
      rw [← Finset.sum_mul]
      unfold paletteIndicator
      rw [sum_paletteIndicator_eq_card]

theorem sum_paletteIndicator_mul_lower {q : ℕ}
    (S : Finset (Fin q)) (x : Fin q → ℝ) {mu eta : ℝ}
    (hx : ∀ c, mu - eta ≤ x c) :
    S.card * (mu - eta) ≤
      ∑ c : Fin q, paletteIndicator S c * x c := by
  calc
    S.card * (mu - eta) =
        ∑ c : Fin q, paletteIndicator S c * (mu - eta) := by
      rw [← Finset.sum_mul]
      unfold paletteIndicator
      rw [sum_paletteIndicator_eq_card]
    _ ≤ _ := by
      apply Finset.sum_le_sum
      intro c _hc
      exact mul_le_mul_of_nonneg_left (hx c) (by
        unfold paletteIndicator
        split <;> norm_num)

theorem sum_offDiagonal_paletteIndicators {q : ℕ}
    (S : Finset (Fin q)) :
    (∑ c : Fin q, ∑ d : Fin q,
      if c = d then 0 else
        paletteIndicator S c * paletteIndicator S d) =
      (S.card : ℝ) * ((S.card : ℝ) - 1) := by
  rw [sum_offDiagonal_mul]
  rw [show (∑ c : Fin q, paletteIndicator S c) = S.card by
    exact sum_paletteIndicator_eq_card S]
  rw [show (∑ c : Fin q, (paletteIndicator S c) ^ 2) = S.card by
    exact sum_sq_paletteIndicator_eq_card S]
  ring

theorem graphOverlapFirst_lower_of_coordinate {q : ℕ}
    (R : Finset G.E) (charge : G.E → ℝ)
    (F : Finset G.E) (color : G.E → Fin q)
    (v : G.V) {W delta1 : ℝ}
    (hq : 0 < q) (hmissing : 0 < G.momentMissingSize F color v)
    (hz : ∀ c,
      W / q - delta1 ≤ G.graphFirstMoment R charge F color v c) :
    W - q * delta1 ≤ G.graphOverlapFirst R charge F color v := by
  let S := G.missingColorsAt F color v
  have hf : (S.card : ℝ) = G.momentMissingSize F color v := rfl
  have hsum := sum_paletteIndicator_mul_lower S
    (G.graphFirstMoment R charge F color v) hz
  unfold graphOverlapFirst
  have hqreal : (0 : ℝ) < q := by exact_mod_cast hq
  rw [← hf]
  have hfreal : (0 : ℝ) < S.card := by
    rw [hf]
    exact hmissing
  calc
    W - (q : ℝ) * delta1 =
        (q : ℝ) / S.card *
          ((S.card : ℝ) * (W / q - delta1)) := by
      field_simp [hqreal.ne', hfreal.ne']
    _ ≤ (q : ℝ) / S.card *
        ∑ c : Fin q, paletteIndicator S c *
          G.graphFirstMoment R charge F color v c :=
      mul_le_mul_of_nonneg_left hsum (div_nonneg hqreal.le hfreal.le)

theorem graphOverlapSecond_upper_of_coordinates {q : ℕ}
    (R : Finset G.E) (charge : G.E → ℝ)
    (F : Finset G.E) (color : G.E → Fin q)
    (v : G.V) {W D delta2 : ℝ}
    (hq : 2 ≤ q) (hmissing : 0 < G.momentMissingSize F color v)
    (hD : 0 ≤ D) (hWD : D ≤ W)
    (hd : ∀ c,
      G.graphDiagonalMoment R charge F color v c ≤ D / q + delta2)
    (hZ : ∀ c d, c ≠ d →
      G.graphPairMoment R charge F color v c d ≤
        (W - D) / ((q : ℝ) * ((q : ℝ) - 1)) + delta2) :
    G.graphOverlapSecond R charge F color v ≤
      W + ((q : ℝ) / G.momentMissingSize F color v) * D +
        (q : ℝ) ^ 2 * delta2 := by
  let S := G.missingColorsAt F color v
  let f : ℝ := S.card
  have hf : f = G.momentMissingSize F color v := rfl
  have hfpos : 0 < f := by
    rw [hf]
    exact hmissing
  have hqreal : (0 : ℝ) < q := by exact_mod_cast (show 0 < q by omega)
  have hqTwo : (2 : ℝ) ≤ (q : ℝ) := by exact_mod_cast hq
  have hqone : (0 : ℝ) < (q : ℝ) - 1 := by linarith
  have hdSum := sum_paletteIndicator_mul_bound S
    (G.graphDiagonalMoment R charge F color v) hd
  have hZSum :
      (∑ c : Fin q, ∑ d : Fin q,
        paletteIndicator S c * paletteIndicator S d *
          G.graphPairMoment R charge F color v c d) ≤
      f * (f - 1) *
        ((W - D) / ((q : ℝ) * ((q : ℝ) - 1)) + delta2) := by
    calc
      (∑ c : Fin q, ∑ d : Fin q,
        paletteIndicator S c * paletteIndicator S d *
          G.graphPairMoment R charge F color v c d) =
        ∑ c : Fin q, ∑ d : Fin q,
          if c = d then 0 else
            paletteIndicator S c * paletteIndicator S d *
              G.graphPairMoment R charge F color v c d := by
        apply Finset.sum_congr rfl
        intro c _hc
        apply Finset.sum_congr rfl
        intro d _hd
        by_cases hcd : c = d
        · subst d
          simp [graphPairMoment, pairMoment]
        · simp [hcd]
      _ ≤ ∑ c : Fin q, ∑ d : Fin q,
          if c = d then 0 else
            paletteIndicator S c * paletteIndicator S d *
              ((W - D) / ((q : ℝ) * ((q : ℝ) - 1)) + delta2) := by
        apply Finset.sum_le_sum
        intro c _hc
        apply Finset.sum_le_sum
        intro d _hd
        by_cases hcd : c = d
        · simp [hcd]
        · simp only [hcd, if_false]
          exact mul_le_mul_of_nonneg_left (hZ c d hcd) (mul_nonneg
            (by unfold paletteIndicator; split <;> norm_num)
            (by unfold paletteIndicator; split <;> norm_num))
      _ = f * (f - 1) *
          ((W - D) / ((q : ℝ) * ((q : ℝ) - 1)) + delta2) := by
        calc
          (∑ c : Fin q, ∑ d : Fin q,
              if c = d then 0 else
                paletteIndicator S c * paletteIndicator S d *
                  ((W - D) / ((q : ℝ) * ((q : ℝ) - 1)) + delta2)) =
              ∑ c : Fin q, ∑ d : Fin q,
                (if c = d then 0 else
                  paletteIndicator S c * paletteIndicator S d) *
                    ((W - D) / ((q : ℝ) * ((q : ℝ) - 1)) + delta2) := by
            apply Finset.sum_congr rfl
            intro c _hc
            apply Finset.sum_congr rfl
            intro d _hd
            by_cases hcd : c = d <;> simp [hcd]
          _ = ∑ c : Fin q,
                (∑ d : Fin q, if c = d then 0 else
                  paletteIndicator S c * paletteIndicator S d) *
                    ((W - D) / ((q : ℝ) * ((q : ℝ) - 1)) + delta2) := by
            apply Finset.sum_congr rfl
            intro c _hc
            exact (Finset.sum_mul (Finset.univ : Finset (Fin q))
              (fun d ↦ if c = d then 0 else
                paletteIndicator S c * paletteIndicator S d)
              ((W - D) / ((q : ℝ) * ((q : ℝ) - 1)) + delta2)).symm
          _ = (∑ c : Fin q, ∑ d : Fin q,
                if c = d then 0 else
                  paletteIndicator S c * paletteIndicator S d) *
                    ((W - D) / ((q : ℝ) * ((q : ℝ) - 1)) + delta2) := by
            exact (Finset.sum_mul (Finset.univ : Finset (Fin q))
              (fun c ↦ ∑ d : Fin q, if c = d then 0 else
                paletteIndicator S c * paletteIndicator S d)
              ((W - D) / ((q : ℝ) * ((q : ℝ) - 1)) + delta2)).symm
          _ = f * (f - 1) *
                ((W - D) / ((q : ℝ) * ((q : ℝ) - 1)) + delta2) := by
            rw [sum_offDiagonal_paletteIndicators]
  unfold graphOverlapSecond
  rw [← hf]
  have hfactor : 0 ≤ ((q : ℝ) / f) ^ 2 := sq_nonneg _
  calc
    ((q : ℝ) / f) ^ 2 *
        ((∑ c : Fin q, paletteIndicator S c *
          G.graphDiagonalMoment R charge F color v c) +
        ∑ c : Fin q, ∑ d : Fin q,
          paletteIndicator S c * paletteIndicator S d *
            G.graphPairMoment R charge F color v c d) ≤
      ((q : ℝ) / f) ^ 2 *
        (f * (D / q + delta2) +
          f * (f - 1) *
            ((W - D) / ((q : ℝ) * ((q : ℝ) - 1)) + delta2)) :=
      mul_le_mul_of_nonneg_left (add_le_add hdSum hZSum) hfactor
    _ ≤ W + ((q : ℝ) / f) * D + (q : ℝ) ^ 2 * delta2 := by
      have hfcard : f ≤ q := by
        have hcard : S.card ≤ q := by
          simpa only [Fintype.card_fin] using Finset.card_le_univ S
        dsimp [f]
        exact_mod_cast hcard
      have hrange : 0 ≤ W - D := sub_nonneg.mpr hWD
      have hratio :
          (q : ℝ) * (f - 1) / (f * ((q : ℝ) - 1)) ≤ 1 := by
        rw [div_le_one (mul_pos hfpos hqone)]
        nlinarith
      have hbase :
          (q : ℝ) * (f - 1) / (f * ((q : ℝ) - 1)) * (W - D) ≤ W - D :=
        by simpa only [one_mul] using
          (mul_le_mul_of_nonneg_right hratio hrange)
      have hexpand :
          ((q : ℝ) / f) ^ 2 *
              (f * (D / q + delta2) +
                f * (f - 1) *
                  ((W - D) / ((q : ℝ) * ((q : ℝ) - 1)) + delta2)) =
            ((q : ℝ) / f) * D + (q : ℝ) ^ 2 * delta2 +
              ((q : ℝ) * (f - 1) / (f * ((q : ℝ) - 1))) * (W - D) := by
        field_simp [hfpos.ne', hqreal.ne', hqone.ne']
        ring
      rw [hexpand]
      linarith

/-- Coordinate mixing bounds imply exactly the scalar squared-error bound. -/
theorem momentSquaredError_le_of_graphCoordinates {q : ℕ}
    (R : Finset G.E) (charge : G.E → ℝ)
    (F : Finset G.E) (color : G.E → Fin q)
    (hmissingAll : ∀ w, 0 < G.momentMissingSize F color w)
    (v : G.V) {W D delta1 delta2 : ℝ}
    (hq : 2 ≤ q) (hW : W = G.restrictedCharge R charge v)
    (hDdef : D = G.graphHarmonicMoment R charge F color v)
    (hD : 0 ≤ D) (hWD : D ≤ W)
    (hz : ∀ c,
      W / q - delta1 ≤ G.graphFirstMoment R charge F color v c)
    (hd : ∀ c,
      G.graphDiagonalMoment R charge F color v c ≤ D / q + delta2)
    (hZ : ∀ c d, c ≠ d →
      G.graphPairMoment R charge F color v c d ≤
        (W - D) / ((q : ℝ) * ((q : ℝ) - 1)) + delta2) :
    G.momentSquaredError R charge F color v ≤
      ((q : ℝ) / G.momentMissingSize F color v) * D +
        (q : ℝ) ^ 2 * delta2 + 2 * (q : ℝ) * delta1 := by
  apply squaredError_le_of_first_second
    (W := W) (D := D) (K := q)
    (first := G.graphOverlapFirst R charge F color v)
    (second := G.graphOverlapSecond R charge F color v)
  · exact G.graphOverlapFirst_lower_of_coordinate R charge F color v
      (by omega) (hmissingAll v) hz
  · exact G.graphOverlapSecond_upper_of_coordinates R charge F color v
      hq (hmissingAll v) hD hWD hd hZ
  · rw [hW, G.momentSquaredError_eq_graphOverlapExpansion
      R charge F color hmissingAll v]

end

end WeightedMultigraph
end WeightedEdgeColoring
