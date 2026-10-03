import WeightedEdgeColoring.UniversalClogScheduleRate
import WeightedEdgeColoring.WeightedMomentEstimateReduction

/-!
# The weighted moment estimate from Kempe pairing schedules

The logarithmic universal schedule gives constant first-coordinate error and
`1/n` second-coordinate error.  The graph overlap expansion then yields the
required `o(n)` squared error uniformly over all vertices.
-/

namespace WeightedEdgeColoring

open scoped BigOperators

noncomputable section

namespace WeightedMultigraph

universe u

variable (G : WeightedMultigraph.{u})

theorem graphHarmonicMoment_eq_of_isProperOn {q : ℕ}
    (R : Finset G.E) (charge : G.E → ℝ) (F : Finset G.E)
    (color next : G.E → Fin q)
    (hcolor : G.IsProperOn F color) (hnext : G.IsProperOn F next)
    (v : G.V) :
    G.graphHarmonicMoment R charge F next v =
      G.graphHarmonicMoment R charge F color v := by
  unfold graphHarmonicMoment WeightedMomentStatistics.harmonicWeight
    graphMomentItemPalette WeightedMomentStatistics.paletteSize
  apply Finset.sum_congr rfl
  intro e _he
  rw [G.card_missingColorsAt_eq_of_isProperOn F next color
    hnext hcolor (G.kempeOtherEndpoint v e.1)]

theorem weightedMomentEstimateMixing_of_kempeSchedule :
    WeightedMomentEstimateMixing.{u} := by
  intro alpha C L delta sigma halpha hC hL hdelta hsigma
  let epsilon1 : ℝ := min delta (sigma / (8 * C))
  let epsilon2 : ℝ := sigma / (4 * C ^ 2)
  have hepsilon1 : 0 < epsilon1 := by dsimp [epsilon1]; positivity
  have hepsilon2 : 0 < epsilon2 := by dsimp [epsilon2]; positivity
  rcases WeightedMultigraph.eventually_exists_clogMixed_coordinates
      halpha hC hL hepsilon1 hepsilon2 with ⟨Nschedule, hschedule⟩
  obtain ⟨Nbase, hNbase⟩ := exists_nat_gt (2 * C / (alpha ^ 2 * sigma))
  refine ⟨max Nschedule (max 1 Nbase), ?_⟩
  intro G n q F R base charge hnLarge hn hqeven hqfour hdisjoint hbase
    hmissing hqLinear hcharge hrestricted hpair
  have hnSchedule : Nschedule ≤ n := (le_max_left _ _).trans hnLarge
  have hnOne : 1 ≤ n :=
    (le_max_left 1 Nbase).trans ((le_max_right Nschedule _).trans hnLarge)
  have hnBase : Nbase ≤ n :=
    (le_max_right 1 Nbase).trans ((le_max_right Nschedule _).trans hnLarge)
  rcases hschedule G n q hnSchedule hn hqeven hqfour hqLinear
      R charge F base hbase hcharge hmissing hrestricted hpair with
    ⟨mixed, hmixed, hzAbs, hdAbs, hZAbs⟩
  have hmissingMixed : ∀ w,
      alpha * n ≤ G.momentMissingSize F mixed w := by
    intro w
    have hcard := G.card_missingColorsAt_eq_of_isProperOn
      F base mixed hbase hmixed w
    unfold WeightedMultigraph.momentMissingSize
    rw [← hcard]
    exact hmissing w
  have hmissingPos : ∀ w, 0 < G.momentMissingSize F mixed w := by
    intro w
    exact lt_of_lt_of_le
      (mul_pos halpha (by exact_mod_cast hn)) (hmissingMixed w)
  have hharmonic : ∀ v,
      G.graphHarmonicMoment R charge F mixed v =
        G.graphHarmonicMoment R charge F base v := by
    intro v
    exact G.graphHarmonicMoment_eq_of_isProperOn R charge F base mixed
      hbase hmixed v
  refine ⟨mixed, hmixed, ?_, ?_⟩
  · intro v c
    rw [← G.graphFirstMoment_eq_momentNeighborPressure R charge F mixed v c]
    have hupper := (le_abs_self
      (G.graphFirstMoment R charge F mixed v c -
        G.restrictedCharge R charge v / q)).trans (hzAbs v c)
    have hepsDelta : epsilon1 ≤ delta := min_le_left _ _
    linarith
  · intro v
    let W := G.restrictedCharge R charge v
    let D := G.graphHarmonicMoment R charge F mixed v
    have hD0 : 0 ≤ D := G.graphHarmonicMoment_nonneg
      R charge F mixed hcharge v
    have hDW : D ≤ W := G.graphHarmonicMoment_le_restrictedCharge
      R charge F mixed hcharge (fun w ↦ by
        have hw := hmissingPos w
        unfold momentMissingSize at hw
        exact_mod_cast hw) v
    have hzLower : ∀ c,
        W / q - epsilon1 ≤ G.graphFirstMoment R charge F mixed v c := by
      intro c
      have := neg_le_of_abs_le (hzAbs v c)
      dsimp [W]
      linarith
    have hdUpper : ∀ c,
        G.graphDiagonalMoment R charge F mixed v c ≤
          D / q + epsilon2 / n := by
      intro c
      have := le_of_abs_le (hdAbs v c)
      dsimp [D]
      rw [hharmonic v]
      linarith
    have hZUpper : ∀ c d, c ≠ d →
        G.graphPairMoment R charge F mixed v c d ≤
          (W - D) / ((q : ℝ) * ((q : ℝ) - 1)) + epsilon2 / n := by
      intro c d hcd
      have := le_of_abs_le (hZAbs v c d)
      dsimp [W, D]
      rw [hharmonic v]
      simp [offDiagonalConstant, hcd] at this
      linarith
    have hsquared := G.momentSquaredError_le_of_graphCoordinates
      R charge F mixed hmissingPos v (W := W) (D := D)
      (delta1 := epsilon1) (delta2 := epsilon2 / n) (by omega) rfl rfl
      hD0 hDW hzLower hdUpper hZUpper
    have hDalpha : D ≤ 1 / alpha :=
      G.graphHarmonicMoment_le_inv_alpha R charge F mixed alpha v
        halpha hn hcharge hmissingMixed (hrestricted v)
    have hratio : (q : ℝ) / G.momentMissingSize F mixed v ≤ C / alpha := by
      have hfpos : 0 < G.momentMissingSize F mixed v := hmissingPos v
      rw [div_le_div_iff₀ hfpos halpha]
      calc
        (q : ℝ) * alpha ≤ (C * n) * alpha :=
          mul_le_mul_of_nonneg_right hqLinear halpha.le
        _ = C * (alpha * n) := by ring
        _ ≤ C * G.momentMissingSize F mixed v :=
          mul_le_mul_of_nonneg_left (hmissingMixed v) hC.le
    have hbaseTerm :
        (q : ℝ) / G.momentMissingSize F mixed v * D ≤ C / alpha ^ 2 := by
      calc
        _ ≤ (C / alpha) * (1 / alpha) :=
          mul_le_mul hratio hDalpha hD0 (by positivity)
        _ = C / alpha ^ 2 := by field_simp [halpha.ne']
    have hqSq : (q : ℝ) ^ 2 ≤ (C * n) ^ 2 :=
      pow_le_pow_left₀ (Nat.cast_nonneg q) hqLinear 2
    have hsecondTerm :
        (q : ℝ) ^ 2 * (epsilon2 / n) ≤ sigma * n / 4 := by
      dsimp [epsilon2]
      have hnreal : (0 : ℝ) < n := by exact_mod_cast hn
      calc
        _ ≤ (C * n) ^ 2 * (sigma / (4 * C ^ 2) / n) :=
          mul_le_mul_of_nonneg_right hqSq (by positivity)
        _ = sigma * n / 4 := by
          field_simp [hC.ne', hnreal.ne']
    have hfirstTerm : 2 * (q : ℝ) * epsilon1 ≤ sigma * n / 4 := by
      have heps : epsilon1 ≤ sigma / (8 * C) := min_le_right _ _
      calc
        _ ≤ 2 * (C * n) * (sigma / (8 * C)) := by
          exact mul_le_mul
            (mul_le_mul_of_nonneg_left hqLinear (by norm_num)) heps
            hepsilon1.le (by positivity)
        _ = sigma * n / 4 := by field_simp [hC.ne']; ring
    have hconstant : C / alpha ^ 2 ≤ sigma * n / 2 := by
      have hlt : 2 * C / (alpha ^ 2 * sigma) < (n : ℝ) :=
        hNbase.trans_le (by exact_mod_cast hnBase)
      rw [div_lt_iff₀ (mul_pos (sq_pos_of_pos halpha) hsigma)] at hlt
      rw [div_le_iff₀ (sq_pos_of_pos halpha)]
      nlinarith
    exact hsquared.trans (by
      calc
        _ ≤ C / alpha ^ 2 + sigma * n / 4 + sigma * n / 4 := by
          exact add_le_add (add_le_add hbaseTerm hsecondTerm) hfirstTerm
        _ ≤ sigma * n := by linarith)

end WeightedMultigraph

theorem weightedMomentEstimateMixing : WeightedMomentEstimateMixing.{u} :=
  WeightedMultigraph.weightedMomentEstimateMixing_of_kempeSchedule

end
end WeightedEdgeColoring
