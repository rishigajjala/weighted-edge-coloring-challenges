import WeightedEdgeColoring.PackingDeviationPolynomialColumn
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

/-!
# Packing deviation after a logarithmic number of stages

The Kempe construction uses a number of pairing stages of order `log n`.
This file gives a deliberately coarse explicit rate.  We bound the logarithm
by a fourth root in the packing deviation and bound the number of stages by
an eighth root.  The resulting accumulated error is `O(n^{-1/4})`.
-/

namespace WeightedEdgeColoring.FinitePartialResamplingNumerics

open Filter
open scoped Topology

noncomputable section

/-- A quadratic column bound has logarithm at most a fixed constant times
the fourth root of `n`. -/
theorem packingLog_quadratic_natCast_le_rpow_quarter
    {C0 : ℝ} (hC0 : 0 ≤ C0) {n : ℕ} (hn : 1 ≤ n) :
    packingLog (C0 * (n : ℝ) ^ 2) ≤
      (Real.log (3 + 16 * C0) + 8) * (n : ℝ) ^ (1 / 4 : ℝ) := by
  let D : ℝ := 3 + 16 * C0
  have hnR : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hnpos : (0 : ℝ) < n := zero_lt_one.trans_le hnR
  have hpow1 : (1 : ℝ) ≤ (n : ℝ) ^ (1 / 4 : ℝ) :=
    Real.one_le_rpow hnR (by norm_num)
  have hDpos : 0 < D := by dsimp [D]; linarith
  have hlogD0 : 0 ≤ Real.log D := Real.log_nonneg (by linarith)
  have hinside :
      3 + 16 * (C0 * (n : ℝ) ^ 2) ≤ D * (n : ℝ) ^ 2 := by
    dsimp [D]
    nlinarith [sq_nonneg ((n : ℝ) - 1)]
  have hlogn :
      Real.log (n : ℝ) ≤ 4 * (n : ℝ) ^ (1 / 4 : ℝ) := by
    have h := Real.log_natCast_le_rpow_div n
      (show (0 : ℝ) < 1 / 4 by norm_num)
    convert h using 1 <;> ring
  calc
    packingLog (C0 * (n : ℝ) ^ 2) =
        Real.log (3 + 16 * (C0 * (n : ℝ) ^ 2)) := rfl
    _ ≤ Real.log (D * (n : ℝ) ^ 2) :=
      Real.log_le_log (by positivity) hinside
    _ = Real.log D + 2 * Real.log (n : ℝ) := by
      rw [Real.log_mul hDpos.ne' (pow_pos hnpos 2).ne', Real.log_pow]
      norm_num
    _ ≤ Real.log D + 8 * (n : ℝ) ^ (1 / 4 : ℝ) := by
      linarith
    _ ≤ (Real.log D + 8) * (n : ℝ) ^ (1 / 4 : ℝ) := by
      nlinarith
    _ = _ := by rfl

/-- Linear rows and quadratic columns give the coarse explicit deviation
bound `O(n^(5/8))`. -/
theorem packingDeviation_linear_quadratic_le_rpow_five_eighth
    {A C0 R C : ℝ} (hA : 0 ≤ A) (hC0 : 0 ≤ C0)
    {n : ℕ} (hn : 1 ≤ n) (hR0 : 0 ≤ R) (hC : 0 ≤ C)
    (hrow : R ≤ A * n) (hcolumn : C ≤ C0 * (n : ℝ) ^ 2) :
    packingDeviation R C ≤
      (4 * Real.sqrt
          (A * (Real.log (3 + 16 * C0) + 8)) +
        4 * (Real.log (3 + 16 * C0) + 8)) *
          (n : ℝ) ^ (5 / 8 : ℝ) := by
  let Lambda : ℝ := Real.log (3 + 16 * C0) + 8
  have hnR : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hnpos : (0 : ℝ) < n := zero_lt_one.trans_le hnR
  have hLambda : 0 ≤ Lambda := by
    dsimp [Lambda]
    have : 0 ≤ Real.log (3 + 16 * C0) :=
      Real.log_nonneg (by linarith)
    linarith
  have hlog0 : 0 ≤ packingLog C := packingLog_nonneg hC
  have hlog : packingLog C ≤ Lambda * (n : ℝ) ^ (1 / 4 : ℝ) := by
    calc
      packingLog C ≤ packingLog (C0 * (n : ℝ) ^ 2) :=
        packingLog_mono hC hcolumn
      _ ≤ (Real.log (3 + 16 * C0) + 8) *
          (n : ℝ) ^ (1 / 4 : ℝ) :=
        packingLog_quadratic_natCast_le_rpow_quarter hC0 hn
      _ = _ := rfl
  have hprod :
      R * packingLog C ≤
        (A * Lambda) * (n : ℝ) ^ (5 / 4 : ℝ) := by
    calc
      R * packingLog C ≤
          (A * n) * (Lambda * (n : ℝ) ^ (1 / 4 : ℝ)) :=
        mul_le_mul hrow hlog hlog0 (mul_nonneg hA (Nat.cast_nonneg n))
      _ = (A * Lambda) * (n : ℝ) ^ (5 / 4 : ℝ) := by
        rw [show (5 / 4 : ℝ) = 1 + 1 / 4 by norm_num,
          Real.rpow_add hnpos]
        simp
        ring
  have hsqrt :
      Real.sqrt (R * packingLog C) ≤
        Real.sqrt (A * Lambda) * (n : ℝ) ^ (5 / 8 : ℝ) := by
    calc
      Real.sqrt (R * packingLog C) ≤
          Real.sqrt ((A * Lambda) * (n : ℝ) ^ (5 / 4 : ℝ)) :=
        Real.sqrt_le_sqrt hprod
      _ = Real.sqrt (A * Lambda) *
          Real.sqrt ((n : ℝ) ^ (5 / 4 : ℝ)) := by
        rw [Real.sqrt_mul (mul_nonneg hA hLambda)]
      _ = Real.sqrt (A * Lambda) *
          (n : ℝ) ^ (5 / 8 : ℝ) := by
        congr 1
        rw [Real.sqrt_eq_rpow, ← Real.rpow_mul (Nat.cast_nonneg n)]
        norm_num
  have hquarter :
      (n : ℝ) ^ (1 / 4 : ℝ) ≤ (n : ℝ) ^ (5 / 8 : ℝ) :=
    Real.rpow_le_rpow_of_exponent_le hnR (by norm_num)
  unfold packingDeviation
  calc
    4 * Real.sqrt (R * packingLog C) + 4 * packingLog C ≤
        4 * (Real.sqrt (A * Lambda) * (n : ℝ) ^ (5 / 8 : ℝ)) +
          4 * (Lambda * (n : ℝ) ^ (1 / 4 : ℝ)) := by
      gcongr
    _ ≤ 4 * (Real.sqrt (A * Lambda) * (n : ℝ) ^ (5 / 8 : ℝ)) +
          4 * (Lambda * (n : ℝ) ^ (5 / 8 : ℝ)) := by
      gcongr
    _ = (4 * Real.sqrt (A * Lambda) + 4 * Lambda) *
          (n : ℝ) ^ (5 / 8 : ℝ) := by ring
    _ = _ := by rfl

/-- If the number of stages is at most a fixed constant times `n^(1/8)`,
then their total error tends to zero.  In particular this applies to every
`O(log n)` stage count. -/
theorem eventually_stage_mul_packingDeviation_le_of_inv_linear
    {B0 A C0 S : ℝ} (hB0 : 0 ≤ B0) (hA : 0 ≤ A)
    (hC0 : 0 ≤ C0) (hS : 0 ≤ S) :
    ∀ epsilon : ℝ, 0 < epsilon →
      ∃ N : ℕ, ∀ n : ℕ, N ≤ n →
      ∀ s : ℕ, ∀ B R C : ℝ,
        0 ≤ B → 0 ≤ R → 0 ≤ C →
        B ≤ B0 / n → R ≤ A * n → C ≤ C0 * (n : ℝ) ^ 2 →
        (s : ℝ) ≤ S * (n : ℝ) ^ (1 / 8 : ℝ) →
        (s : ℝ) * B * packingDeviation R C ≤ epsilon := by
  intro epsilon hepsilon
  let Lambda : ℝ := Real.log (3 + 16 * C0) + 8
  let Q : ℝ := 4 * Real.sqrt (A * Lambda) + 4 * Lambda
  let T : ℝ := S * B0 * Q
  have hLambda : 0 ≤ Lambda := by
    dsimp [Lambda]
    have : 0 ≤ Real.log (3 + 16 * C0) :=
      Real.log_nonneg (by linarith)
    linarith
  have hQ : 0 ≤ Q := by dsimp [Q]; positivity
  have hT : 0 ≤ T := by dsimp [T]; positivity
  have ht0 : Tendsto
      (fun n : ℕ ↦ (n : ℝ) ^ (-(1 / 4 : ℝ))) atTop (𝓝 0) :=
    (tendsto_rpow_neg_atTop (show (0 : ℝ) < 1 / 4 by norm_num)).comp
      tendsto_natCast_atTop_atTop
  have ht : Tendsto
      (fun n : ℕ ↦ T * (n : ℝ) ^ (-(1 / 4 : ℝ))) atTop (𝓝 0) :=
    by simpa using (tendsto_const_nhds.mul ht0)
  have hevent : ∀ᶠ n : ℕ in atTop,
      T * (n : ℝ) ^ (-(1 / 4 : ℝ)) < epsilon := by
    have hball := ht.eventually (Metric.ball_mem_nhds (0 : ℝ) hepsilon)
    filter_upwards [hball] with n hnball
    simpa [Metric.mem_ball, Real.dist_eq, abs_mul, abs_of_nonneg hT,
      abs_of_nonneg (Real.rpow_nonneg _ _)] using hnball
  rcases (eventually_atTop.1 hevent) with ⟨N0, hN0⟩
  refine ⟨max 1 N0, ?_⟩
  intro n hn s B R C hB hR hC hBinv hRlin hCquad hs
  have hn1 : 1 ≤ n := (le_max_left 1 N0).trans hn
  have hn0 : N0 ≤ n := (le_max_right 1 N0).trans hn
  have hnpos : (0 : ℝ) < n := by exact_mod_cast (Nat.zero_lt_of_lt hn1)
  have hnnonneg : (0 : ℝ) ≤ n := hnpos.le
  have hnEighth0 : 0 ≤ (n : ℝ) ^ (1 / 8 : ℝ) :=
    Real.rpow_nonneg hnnonneg _
  have hdev := packingDeviation_linear_quadratic_le_rpow_five_eighth
    hA hC0 hn1 hR hC hRlin hCquad
  have hlog0C : 0 ≤ packingLog C := packingLog_nonneg hC
  have hdev0 : 0 ≤ packingDeviation R C := by
    unfold packingDeviation
    exact add_nonneg
      (mul_nonneg (by norm_num) (Real.sqrt_nonneg _))
      (mul_nonneg (by norm_num) hlog0C)
  have hpowers :
      ((n : ℝ) ^ (1 / 8 : ℝ) * (n : ℝ) ^ (5 / 8 : ℝ)) /
          (n : ℝ) =
        (n : ℝ) ^ (-(1 / 4 : ℝ)) := by
    calc
      ((n : ℝ) ^ (1 / 8 : ℝ) * (n : ℝ) ^ (5 / 8 : ℝ)) /
          (n : ℝ) =
        (n : ℝ) ^ ((1 / 8 : ℝ) + 5 / 8) /
          (n : ℝ) ^ (1 : ℝ) := by
            rw [Real.rpow_add hnpos, Real.rpow_one]
      _ = (n : ℝ) ^ (((1 / 8 : ℝ) + 5 / 8) - 1) := by
        rw [Real.rpow_sub hnpos]
      _ = (n : ℝ) ^ (-(1 / 4 : ℝ)) := by norm_num
  calc
    (s : ℝ) * B * packingDeviation R C ≤
        (S * (n : ℝ) ^ (1 / 8 : ℝ)) *
          (B0 / n) * (Q * (n : ℝ) ^ (5 / 8 : ℝ)) := by
      exact mul_le_mul
        (mul_le_mul hs hBinv hB (mul_nonneg hS hnEighth0))
        (by simpa [Q, Lambda] using hdev) hdev0
        (mul_nonneg (mul_nonneg hS hnEighth0)
          (div_nonneg hB0 hnpos.le))
    _ = T * (n : ℝ) ^ (-(1 / 4 : ℝ)) := by
      dsimp [T]
      rw [← hpowers]
      field_simp
    _ ≤ epsilon := (hN0 n hn0).le

end

end WeightedEdgeColoring.FinitePartialResamplingNumerics
