import WeightedEdgeColoring.PackingDeviationLogStageRate
import Mathlib.Analysis.SpecialFunctions.Log.Base

/-!
# A coarse power bound for a binary logarithmic schedule

The universal pairing argument uses `Nat.clog 2 n` stages.  The accumulated
selector-error lemma is stated for any stage count bounded by a constant
times `n^(1/8)`.  This file supplies that elementary comparison with an
explicit constant.
-/

namespace WeightedEdgeColoring.FinitePartialResamplingNumerics

noncomputable section

/-- The binary ceiling logarithm is eventually much smaller than an eighth
root; the displayed estimate is valid already for every positive `n`. -/
theorem natCast_clog_two_le_rpow_eighth
    {n : ℕ} (hn : 1 ≤ n) :
    ((Nat.clog 2 n : ℕ) : ℝ) ≤
      (8 / Real.log 2 + 1) * (n : ℝ) ^ (1 / 8 : ℝ) := by
  have hnR : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hroot : (1 : ℝ) ≤ (n : ℝ) ^ (1 / 8 : ℝ) :=
    Real.one_le_rpow hnR (by norm_num)
  have hlogTwo : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hlogn :
      Real.log (n : ℝ) ≤ 8 * (n : ℝ) ^ (1 / 8 : ℝ) := by
    have h := Real.log_natCast_le_rpow_div n
      (show (0 : ℝ) < 1 / 8 by norm_num)
    convert h using 1 <;> ring
  have hlogb0 : 0 ≤ Real.logb 2 (n : ℝ) :=
    Real.logb_nonneg (by norm_num) hnR
  have hceil :
      ((Nat.clog 2 n : ℕ) : ℝ) ≤ Real.logb 2 (n : ℝ) + 1 := by
    rw [← Real.natCeil_logb_natCast]
    exact (Nat.ceil_lt_add_one hlogb0).le
  have hlogb :
      Real.logb 2 (n : ℝ) ≤
        (8 / Real.log 2) * (n : ℝ) ^ (1 / 8 : ℝ) := by
    rw [Real.logb]
    calc
      Real.log (n : ℝ) / Real.log 2 ≤
          (8 * (n : ℝ) ^ (1 / 8 : ℝ)) / Real.log 2 :=
        div_le_div_of_nonneg_right hlogn hlogTwo.le
      _ = (8 / Real.log 2) * (n : ℝ) ^ (1 / 8 : ℝ) := by ring
  calc
    ((Nat.clog 2 n : ℕ) : ℝ) ≤
        Real.logb 2 (n : ℝ) + 1 := hceil
    _ ≤ (8 / Real.log 2) * (n : ℝ) ^ (1 / 8 : ℝ) + 1 :=
      by simpa [add_comm] using add_le_add_right hlogb 1
    _ ≤ (8 / Real.log 2 + 1) * (n : ℝ) ^ (1 / 8 : ℝ) := by
      have hcoef : 0 ≤ 8 / Real.log 2 := by positivity
      nlinarith

/-- The concrete sixteen-fold schedule used in the moment proof satisfies
the stage-count hypothesis of the accumulated packing-deviation estimate. -/
theorem natCast_sixteen_mul_clog_two_le_rpow_eighth
    {n : ℕ} (hn : 1 ≤ n) :
    ((16 * Nat.clog 2 n : ℕ) : ℝ) ≤
      (16 * (8 / Real.log 2 + 1)) *
        (n : ℝ) ^ (1 / 8 : ℝ) := by
  have h := natCast_clog_two_le_rpow_eighth hn
  push_cast
  nlinarith

end

end WeightedEdgeColoring.FinitePartialResamplingNumerics
