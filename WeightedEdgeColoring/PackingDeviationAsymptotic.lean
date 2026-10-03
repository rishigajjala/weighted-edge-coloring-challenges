import WeightedEdgeColoring.FinitePartialResamplingNumerics
import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-!
# The packing deviation is sublinear

The partial-resampling selector pays

`4 * sqrt (R * log (3 + 16 C)) + 4 * log (3 + 16 C)`.

In every application below, both `R` and `C` are at most fixed constants
times the palette size.  This file records the elementary, uniform fact that
the resulting loss is `o(n)`.  The proof uses the explicit bound
`log x <= 2 sqrt x`; no asymptotic library is hidden in the argument.
-/

namespace WeightedEdgeColoring.FinitePartialResamplingNumerics

noncomputable section

/-- Once `n` is at least `delta^{-2}`, its square root is at most
`delta * n`. -/
theorem sqrt_natCast_le_mul_of_inv_sq_le {delta : ℝ} (hdelta : 0 < delta)
    {n : ℕ} (hn : 1 / delta ^ 2 ≤ (n : ℝ)) :
    Real.sqrt (n : ℝ) ≤ delta * n := by
  have hn0 : 0 ≤ (n : ℝ) := Nat.cast_nonneg n
  have hdelta2 : 0 < delta ^ 2 := sq_pos_of_pos hdelta
  have hone : 1 ≤ (n : ℝ) * delta ^ 2 :=
    (div_le_iff₀ hdelta2).mp hn
  have hsqrt0 : 0 ≤ Real.sqrt (n : ℝ) := Real.sqrt_nonneg _
  have hrhs0 : 0 ≤ delta * (n : ℝ) := mul_nonneg hdelta.le hn0
  have hsqrt_sq : (Real.sqrt (n : ℝ)) ^ 2 = (n : ℝ) :=
    Real.sq_sqrt hn0
  nlinarith

/-- A convenient linear upper bound on the logarithm in `packingDeviation`.
The coefficient can be made arbitrarily small by taking `n` large. -/
theorem packingLog_mul_natCast_le
    {C delta : ℝ} (hC : 0 ≤ C) (hdelta : 0 < delta)
    {n : ℕ} (hn_one : 1 ≤ n)
    (hn_delta : 1 / delta ^ 2 ≤ (n : ℝ)) :
    packingLog (C * n) ≤
      2 * Real.sqrt (3 + 16 * C) * delta * n := by
  let y : ℝ := 3 + 16 * (C * n)
  let D : ℝ := 3 + 16 * C
  have hn0 : 0 ≤ (n : ℝ) := Nat.cast_nonneg n
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast hn_one
  have hD0 : 0 ≤ D := by dsimp [D]; positivity
  have hy0 : 0 ≤ y := by dsimp [y]; positivity
  have hyD : y ≤ D * n := by
    dsimp [y, D]
    nlinarith
  have hlog : Real.log y ≤ 2 * Real.sqrt y := by
    have h := Real.log_le_rpow_div hy0 (show (0 : ℝ) < 1 / 2 by norm_num)
    rw [← Real.sqrt_eq_rpow] at h
    nlinarith
  have hsqrt_y : Real.sqrt y ≤ Real.sqrt D * Real.sqrt (n : ℝ) := by
    calc
      Real.sqrt y ≤ Real.sqrt (D * n) := Real.sqrt_le_sqrt hyD
      _ = Real.sqrt D * Real.sqrt (n : ℝ) := by
        rw [Real.sqrt_mul hD0]
  have hsqrt_n := sqrt_natCast_le_mul_of_inv_sq_le hdelta hn_delta
  unfold packingLog
  change Real.log y ≤ _
  calc
    Real.log y ≤ 2 * Real.sqrt y := hlog
    _ ≤ 2 * (Real.sqrt D * Real.sqrt (n : ℝ)) := by gcongr
    _ = (2 * Real.sqrt D) * Real.sqrt (n : ℝ) := by ring
    _ ≤ (2 * Real.sqrt D) * (delta * n) :=
      mul_le_mul_of_nonneg_left hsqrt_n
        (mul_nonneg (by norm_num) (Real.sqrt_nonneg D))
    _ = 2 * Real.sqrt (3 + 16 * C) * delta * n := by
      simp [D]
      ring

/-- If the logarithmic term is at most `lambda * n`, then the complete
packing deviation has the displayed linear bound. -/
theorem packingDeviation_mul_natCast_le_of_log
    {A C lambda : ℝ} (hA : 0 ≤ A) (hC : 0 ≤ C) (hlambda : 0 ≤ lambda)
    {n : ℕ}
    (hlog : packingLog (C * n) ≤ lambda * n) :
    packingDeviation (A * n) (C * n) ≤
      (4 * Real.sqrt (A * lambda) + 4 * lambda) * n := by
  have hn0 : 0 ≤ (n : ℝ) := Nat.cast_nonneg n
  have hlog0 : 0 ≤ packingLog (C * n) :=
    packingLog_nonneg (mul_nonneg hC hn0)
  have hinside0 : 0 ≤ (A * n) * packingLog (C * n) :=
    mul_nonneg (mul_nonneg hA hn0) hlog0
  have hAlambda0 : 0 ≤ A * lambda := mul_nonneg hA hlambda
  have hprod :
      (A * n) * packingLog (C * n) ≤ (A * lambda) * (n : ℝ) ^ 2 := by
    calc
      (A * n) * packingLog (C * n) ≤ (A * n) * (lambda * n) := by
        exact mul_le_mul_of_nonneg_left hlog (mul_nonneg hA hn0)
      _ = (A * lambda) * (n : ℝ) ^ 2 := by ring
  have hsqrt0 := Real.sqrt_nonneg ((A * n) * packingLog (C * n))
  have hrhs0 : 0 ≤ Real.sqrt (A * lambda) * (n : ℝ) :=
    mul_nonneg (Real.sqrt_nonneg _) hn0
  have hsqrt_sq :
      (Real.sqrt ((A * n) * packingLog (C * n))) ^ 2 =
        (A * n) * packingLog (C * n) := Real.sq_sqrt hinside0
  have hrhs_sq :
      (Real.sqrt (A * lambda) * (n : ℝ)) ^ 2 =
        (A * lambda) * (n : ℝ) ^ 2 := by
    rw [mul_pow, Real.sq_sqrt hAlambda0]
  have hsqrt :
      Real.sqrt ((A * n) * packingLog (C * n)) ≤
        Real.sqrt (A * lambda) * n := by
    nlinarith
  unfold packingDeviation
  calc
    4 * Real.sqrt ((A * n) * packingLog (C * n)) +
          4 * packingLog (C * n) ≤
        4 * (Real.sqrt (A * lambda) * n) + 4 * (lambda * n) := by
      gcongr
    _ = (4 * Real.sqrt (A * lambda) + 4 * lambda) * n := by ring

/-- The deviation paid by the categorical packing selector is uniformly
sublinear when its row and column parameters grow at most linearly. -/
theorem packingDeviation_mul_natCast_sublinear
    {A C : ℝ} (hA : 0 ≤ A) (hC : 0 ≤ C) :
    ∀ epsilon : ℝ, 0 < epsilon → ∃ N : ℕ, ∀ n : ℕ, N ≤ n →
      packingDeviation (A * n) (C * n) ≤ epsilon * n := by
  intro epsilon hepsilon
  let Abar : ℝ := A + 1
  let lambda : ℝ := min (epsilon ^ 2 / (1024 * Abar)) (epsilon / 16)
  have hAbar : 0 < Abar := by dsimp [Abar]; linarith
  have hlambda : 0 < lambda := by
    dsimp [lambda]
    exact lt_min (div_pos (sq_pos_of_pos hepsilon) (mul_pos (by norm_num) hAbar))
      (div_pos hepsilon (by norm_num))
  let D : ℝ := 3 + 16 * C
  have hD : 0 < D := by dsimp [D]; linarith
  let delta : ℝ := lambda / (2 * Real.sqrt D)
  have hdelta : 0 < delta := by
    dsimp [delta]
    exact div_pos hlambda (mul_pos (by norm_num) (Real.sqrt_pos.2 hD))
  let N : ℕ := Nat.ceil (max 1 (1 / delta ^ 2))
  refine ⟨N, ?_⟩
  intro n hn
  have hmax : max 1 (1 / delta ^ 2) ≤ (n : ℝ) := by
    calc
      max 1 (1 / delta ^ 2) ≤ (N : ℝ) := Nat.le_ceil _
      _ ≤ n := by exact_mod_cast hn
  have hn_one : 1 ≤ n := by
    exact_mod_cast (le_max_left 1 (1 / delta ^ 2) |>.trans hmax)
  have hn_delta : 1 / delta ^ 2 ≤ (n : ℝ) :=
    (le_max_right 1 (1 / delta ^ 2)).trans hmax
  have hlog := packingLog_mul_natCast_le hC hdelta hn_one hn_delta
  have hcoeflog : 2 * Real.sqrt (3 + 16 * C) * delta = lambda := by
    dsimp [delta, D]
    have hsqrt_ne : Real.sqrt (3 + 16 * C) ≠ 0 :=
      ne_of_gt (Real.sqrt_pos.2 (by linarith))
    field_simp
  have hlog' : packingLog (C * n) ≤ lambda * n := by
    rw [hcoeflog] at hlog
    exact hlog
  have hdev := packingDeviation_mul_natCast_le_of_log hA hC hlambda.le hlog'
  have hlambda_sq : lambda ≤ epsilon ^ 2 / (1024 * Abar) := by
    exact min_le_left _ _
  have hlambda_lin : lambda ≤ epsilon / 16 := min_le_right _ _
  have hA_le : A ≤ Abar := by dsimp [Abar]; linarith
  have hAlambda : A * lambda ≤ epsilon ^ 2 / 1024 := by
    calc
      A * lambda ≤ Abar * lambda :=
        mul_le_mul_of_nonneg_right hA_le hlambda.le
      _ ≤ Abar * (epsilon ^ 2 / (1024 * Abar)) :=
        mul_le_mul_of_nonneg_left hlambda_sq hAbar.le
      _ = epsilon ^ 2 / 1024 := by field_simp
  have hsqrt_bound : Real.sqrt (A * lambda) ≤ epsilon / 32 := by
    have h0 : 0 ≤ A * lambda := mul_nonneg hA hlambda.le
    have he0 : 0 ≤ epsilon / 32 := by positivity
    have hsquare : (epsilon / 32) ^ 2 = epsilon ^ 2 / 1024 := by ring
    rw [← hsquare] at hAlambda
    exact Real.sqrt_le_iff.mpr ⟨he0, hAlambda⟩
  have hcoef : 4 * Real.sqrt (A * lambda) + 4 * lambda ≤ epsilon := by
    nlinarith
  calc
    packingDeviation (A * n) (C * n) ≤
        (4 * Real.sqrt (A * lambda) + 4 * lambda) * n := hdev
    _ ≤ epsilon * n :=
      mul_le_mul_of_nonneg_right hcoef (Nat.cast_nonneg n)

end

end WeightedEdgeColoring.FinitePartialResamplingNumerics
