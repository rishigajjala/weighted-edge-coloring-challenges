import WeightedEdgeColoring.DyadicSimpleScales
import WeightedEdgeColoring.RankThreeIsolatedVariableSlackScalarClosure
import Mathlib.Analysis.Complex.ExponentialBounds

/-!
# Corrected isolated moments on the simple-graph polynomial scales
-/

namespace WeightedEdgeColoring

noncomputable section

/-- The exact base-two moment envelope is at most twice the earlier
`8 log(d+1)+1` envelope. -/
theorem isolatedVariableMomentUpper_le_two_sharpConcrete
    (d : ℕ) :
    isolatedVariableMomentUpper d ≤ 2 * sharpConcreteMomentUpper d := by
  have hlog2 : (1 / 2 : ℝ) < Real.log 2 := by
    exact Real.log_two_gt_d9.trans_le' (by norm_num)
  have hlog2pos : 0 < Real.log 2 := by positivity
  have hlogd : 0 ≤ Real.log ((d : ℝ) + 1) := by
    apply Real.log_nonneg
    exact_mod_cast Nat.succ_le_succ (Nat.zero_le d)
  unfold isolatedVariableMomentUpper
  rw [show (isolatedVariableZ d + Real.log 2) / Real.log 2 + 1 =
      (isolatedVariableZ d + 2 * Real.log 2) / Real.log 2 by
    field_simp [hlog2pos.ne']
    <;> ring]
  unfold isolatedVariableZ sharpConcreteMomentUpper
  apply (div_le_iff₀ hlog2pos).2
  nlinarith [mul_nonneg hlogd
    (by linarith [hlog2] : 0 ≤ 2 * Real.log 2 - 1)]

/-- The honest squared-codegree condition for the corrected isolated moment
holds on the existing `m^30`/`m^14` scale. -/
theorem eventually_dyadicSimple_corrected_square_ratio
    (A : ℕ) (alpha gamma : ℝ)
    (halpha : 0 < alpha) (hgamma : 0 < gamma) :
    ∀ᶠ m : ℕ in Filter.atTop, ∀ d lambda : ℕ,
      0 < d → 0 < m →
      lambda ≤ dyadicSimpleCodegreeScale A m →
      dyadicSimpleQuantizationScale m ≤ 2 * d →
      d ≤ (m + 1) ^ 30 →
      (lambda : ℝ) ^ 2 * isolatedVariableMomentUpper d ^ 2 ≤
        variableSlackBeta0 alpha gamma * d := by
  have halphaQuarter : 0 < alpha / 4 := div_pos halpha (by norm_num)
  filter_upwards [eventually_dyadicSimple_square_ratio A (alpha / 4) gamma
      halphaQuarter hgamma] with m hm
  intro d lambda hd hmpos hlambda hdLower hdUpper
  have hold := hm d lambda hd hmpos hlambda hdLower hdUpper
  have hU := isolatedVariableMomentUpper_le_two_sharpConcrete d
  have hU0 := isolatedVariableMomentUpper_nonneg d
  have hsq : isolatedVariableMomentUpper d ^ 2 ≤
      4 * sharpConcreteMomentUpper d ^ 2 := by
    calc
      isolatedVariableMomentUpper d ^ 2 ≤
          (2 * sharpConcreteMomentUpper d) ^ 2 :=
        pow_le_pow_left₀ hU0 hU 2
      _ = 4 * sharpConcreteMomentUpper d ^ 2 := by ring
  have hlambdaSq : 0 ≤ (lambda : ℝ) ^ 2 := sq_nonneg _
  calc
    (lambda : ℝ) ^ 2 * isolatedVariableMomentUpper d ^ 2 ≤
        4 * ((lambda : ℝ) ^ 2 * sharpConcreteMomentUpper d ^ 2) := by
      calc
        (lambda : ℝ) ^ 2 * isolatedVariableMomentUpper d ^ 2 ≤
            (lambda : ℝ) ^ 2 *
              (4 * sharpConcreteMomentUpper d ^ 2) :=
          mul_le_mul_of_nonneg_left hsq hlambdaSq
        _ = 4 * ((lambda : ℝ) ^ 2 *
              sharpConcreteMomentUpper d ^ 2) := by ring
    _ ≤ 4 * (variableSlackBeta0 (alpha / 4) gamma * d) := by
      exact mul_le_mul_of_nonneg_left hold (by norm_num)
    _ = variableSlackBeta0 alpha gamma * d := by
      unfold variableSlackBeta0
      ring

end

end WeightedEdgeColoring
