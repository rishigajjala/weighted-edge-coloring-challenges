import WeightedEdgeColoring.FinitePartialResamplingNumerics

/-!
# Charge bounds for the mass-sensitive selector

This file proves the numerical estimates behind the partial-resampling
parameters.  Write

`theta = min 1 (sqrt (log (3 + 16 C) / R))`

and let `A = (1 + theta) (exp theta - 1) R`.  The chosen threshold satisfies

`exp (theta * threshold) = exp A * (3 + 16 C)`.

Consequently the normalized self-charge is at most `1 / (2 + 16 C)`, hence
at most one half.  The normalized source-charge factor is at most
`2 theta / (2 + 16 C)`; multiplying by a column mass `C` costs at most
`theta / 8`.  These are the elementary inequalities needed when the finite
partial-resampling criterion is applied later.
-/

namespace WeightedEdgeColoring.FinitePartialResamplingNumerics

/-- Exponent contributed by the inflated row mean. -/
noncomputable def packingExponent (R C : ℝ) : ℝ :=
  (1 + packingTheta R C) * (Real.exp (packingTheta R C) - 1) * R

theorem packingExponent_nonneg {R C : ℝ} (hR : 0 < R) (hC : 0 ≤ C) :
    0 ≤ packingExponent R C := by
  have htheta := packingTheta_nonneg hR hC
  have hexp : 0 ≤ Real.exp (packingTheta R C) - 1 :=
    sub_nonneg.mpr (Real.one_le_exp htheta)
  unfold packingExponent
  exact mul_nonneg (mul_nonneg (by linarith) hexp) hR.le

theorem packingThreshold_eq_exponent_div (R C : ℝ) :
    packingThreshold R C =
      (packingExponent R C + packingLog C) / packingTheta R C := by
  simp [packingThreshold, packingExponent]

theorem packingThreshold_pos {R C : ℝ} (hR : 0 < R) (hC : 0 ≤ C) :
    0 < packingThreshold R C := by
  rw [packingThreshold_eq_exponent_div]
  exact div_pos
    (add_pos_of_nonneg_of_pos (packingExponent_nonneg hR hC)
      (packingLog_pos hC))
    (packingTheta_pos hR hC)

theorem packingTheta_mul_threshold {R C : ℝ} (hR : 0 < R)
    (hC : 0 ≤ C) :
    packingTheta R C * packingThreshold R C =
      packingExponent R C + packingLog C := by
  rw [packingThreshold_eq_exponent_div]
  field_simp [ne_of_gt (packingTheta_pos hR hC)]

theorem exp_packingTheta_mul_threshold {R C : ℝ} (hR : 0 < R)
    (hC : 0 ≤ C) :
    Real.exp (packingTheta R C * packingThreshold R C) =
      Real.exp (packingExponent R C) * (3 + 16 * C) := by
  rw [packingTheta_mul_threshold hR hC, Real.exp_add, exp_packingLog hC]

theorem packingDenominator_pos {R C : ℝ} (hR : 0 < R) (hC : 0 ≤ C) :
    0 < Real.exp (packingTheta R C * packingThreshold R C) - 1 := by
  exact sub_pos.mpr (Real.one_lt_exp_iff.mpr
    (mul_pos (packingTheta_pos hR hC) (packingThreshold_pos hR hC)))

/-- The threshold leaves a factor `2 + 16 C` below the exponential
denominator. -/
theorem packingDenominator_lower {R C : ℝ} (hR : 0 < R) (hC : 0 ≤ C) :
    Real.exp (packingExponent R C) * (2 + 16 * C) ≤
      Real.exp (packingTheta R C * packingThreshold R C) - 1 := by
  rw [exp_packingTheta_mul_threshold hR hC]
  have hone : 1 ≤ Real.exp (packingExponent R C) :=
    Real.one_le_exp (packingExponent_nonneg hR hC)
  nlinarith

/-- Normalized self-charge factor for one row. -/
theorem packingSelfFactor_le {R C : ℝ} (hR : 0 < R) (hC : 0 ≤ C) :
    Real.exp (packingExponent R C) /
        (Real.exp (packingTheta R C * packingThreshold R C) - 1) ≤
      1 / (2 + 16 * C) := by
  have hden := packingDenominator_pos hR hC
  have hbase : 0 < 2 + 16 * C := by linarith
  apply (div_le_iff₀ hden).2
  have haux : Real.exp (packingExponent R C) ≤
      (Real.exp (packingTheta R C * packingThreshold R C) - 1) /
        (2 + 16 * C) :=
    (le_div_iff₀ hbase).2 (packingDenominator_lower hR hC)
  simpa [div_eq_mul_inv, mul_comm] using haux

theorem packingSelfFactor_le_half {R C : ℝ} (hR : 0 < R)
    (hC : 0 ≤ C) :
    Real.exp (packingExponent R C) /
        (Real.exp (packingTheta R C * packingThreshold R C) - 1) ≤
      1 / 2 := by
  refine (packingSelfFactor_le hR hC).trans ?_
  exact div_le_div_of_nonneg_left zero_le_one (by norm_num) (by linarith)

/-- Normalized source-charge factor before multiplying by the physical
source--state column mass. -/
theorem packingSourceFactor_le {R C : ℝ} (hR : 0 < R) (hC : 0 ≤ C) :
    ((Real.exp (packingTheta R C) - 1) * Real.exp (packingExponent R C)) /
        (Real.exp (packingTheta R C * packingThreshold R C) - 1) ≤
      2 * packingTheta R C / (2 + 16 * C) := by
  have hkernel := exp_packingTheta_sub_one_le_two_mul hR hC
  have hratio := packingSelfFactor_le hR hC
  have hkernel0 : 0 ≤ Real.exp (packingTheta R C) - 1 :=
    sub_nonneg.mpr (Real.one_le_exp (packingTheta_nonneg hR hC))
  have hinv0 : 0 ≤ (1 : ℝ) / (2 + 16 * C) := by positivity
  calc
    ((Real.exp (packingTheta R C) - 1) * Real.exp (packingExponent R C)) /
          (Real.exp (packingTheta R C * packingThreshold R C) - 1) =
        (Real.exp (packingTheta R C) - 1) *
          (Real.exp (packingExponent R C) /
            (Real.exp (packingTheta R C * packingThreshold R C) - 1)) := by
              ring
    _ ≤ (Real.exp (packingTheta R C) - 1) * (1 / (2 + 16 * C)) :=
      mul_le_mul_of_nonneg_left hratio hkernel0
    _ ≤ (2 * packingTheta R C) * (1 / (2 + 16 * C)) :=
      mul_le_mul_of_nonneg_right hkernel hinv0
    _ = 2 * packingTheta R C / (2 + 16 * C) := by ring

/-- Summing the source factor over one source--state column of total mass at
most `C` costs at most `theta / 8`. -/
theorem packingSourceColumnFactor_le {R C : ℝ} (hR : 0 < R) (hC : 0 ≤ C) :
    (2 * packingTheta R C / (2 + 16 * C)) * C ≤
      packingTheta R C / 8 := by
  have hbase : 0 < 2 + 16 * C := by linarith
  rw [show (2 * packingTheta R C / (2 + 16 * C)) * C =
      (2 * packingTheta R C * C) / (2 + 16 * C) by ring]
  apply (div_le_iff₀ hbase).2
  have htheta := packingTheta_nonneg hR hC
  nlinarith

/-- The term `theta * R` never exceeds the geometric-mean scale. -/
theorem packingTheta_mul_le_sqrt_mul {R C : ℝ} (hR : 0 < R)
    (hC : 0 ≤ C) :
    packingTheta R C * R ≤ Real.sqrt (R * packingLog C) := by
  have hsq := packingTheta_sq_le_log_div hR hC
  have hmul := mul_le_mul_of_nonneg_right hsq (sq_nonneg R)
  have hsquare : (packingTheta R C * R) ^ 2 ≤ R * packingLog C := by
    calc
      (packingTheta R C * R) ^ 2 =
          packingTheta R C ^ 2 * R ^ 2 := by ring
      _ ≤ (packingLog C / R) * R ^ 2 := hmul
      _ = R * packingLog C := by
        field_simp [ne_of_gt hR]
        <;> ring
  have hleft : 0 ≤ packingTheta R C * R :=
    mul_nonneg (packingTheta_nonneg hR hC) hR.le
  have hinside : 0 ≤ R * packingLog C :=
    mul_nonneg hR.le (packingLog_nonneg hC)
  have hsqrt := Real.sqrt_nonneg (R * packingLog C)
  have hsqrt_sq := Real.sq_sqrt hinside
  nlinarith

/-- The logarithmic part divided by `theta` is controlled by the same
geometric-mean scale, plus one copy of the logarithm. -/
theorem packingLog_div_theta_le {R C : ℝ} (hR : 0 < R) (hC : 0 ≤ C) :
    packingLog C / packingTheta R C ≤
      Real.sqrt (R * packingLog C) + packingLog C := by
  let s := Real.sqrt (packingLog C / R)
  by_cases hlarge : (1 : ℝ) ≤ s
  · have htheta : packingTheta R C = 1 := by
      simp [packingTheta, s, min_eq_left hlarge]
    rw [htheta]
    have hsqrt := Real.sqrt_nonneg (R * packingLog C)
    linarith
  · have hs_le : s ≤ 1 := le_of_not_ge hlarge
    have htheta : packingTheta R C = s := by
      simp [packingTheta, s, min_eq_right hs_le]
    have hs_pos : 0 < s := by
      dsimp [s]
      exact Real.sqrt_pos.2 (div_pos (packingLog_pos hC) hR)
    have hs_sq : s ^ 2 = packingLog C / R := by
      dsimp [s]
      exact Real.sq_sqrt (div_nonneg (packingLog_nonneg hC) hR.le)
    have hidentity : packingLog C / s = s * R := by
      apply (div_eq_iff (ne_of_gt hs_pos)).2
      have hRne : R ≠ 0 := ne_of_gt hR
      calc
        packingLog C = (packingLog C / R) * R := by
          field_simp [hRne]
        _ = s ^ 2 * R := by rw [← hs_sq]
        _ = s * R * s := by ring
    rw [htheta, hidentity]
    have hgeom := packingTheta_mul_le_sqrt_mul hR hC
    rw [htheta] at hgeom
    nlinarith [packingLog_nonneg hC]

/-- The chosen threshold has the advertised Bernstein-size deviation. -/
theorem packingThreshold_le_base_add_deviation {R C : ℝ} (hR : 0 < R)
    (hC : 0 ≤ C) :
    packingThreshold R C ≤ R + packingDeviation R C := by
  let theta := packingTheta R C
  let L := packingLog C
  have htheta_pos : 0 < theta := by
    simpa [theta] using packingTheta_pos hR hC
  have htheta0 : 0 ≤ theta := htheta_pos.le
  have hR0 : 0 ≤ R := hR.le
  have hkernel : Real.exp theta - 1 ≤ theta + theta ^ 2 := by
    simpa [theta] using exp_packingTheta_sub_one_le hR hC
  have hscaled :
      (1 + theta) * (Real.exp theta - 1) * R ≤
        (1 + theta) * (theta + theta ^ 2) * R := by
    exact mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left hkernel (by linarith)) hR0
  have hfirst : packingThreshold R C ≤
      ((1 + theta) * (theta + theta ^ 2) * R + L) / theta := by
    rw [packingThreshold_eq_exponent_div]
    dsimp [packingExponent]
    simpa [theta, L, add_comm] using div_le_div_of_nonneg_right
      (add_le_add_right hscaled L) htheta0
  have hrewrite :
      ((1 + theta) * (theta + theta ^ 2) * R + L) / theta =
        R + 2 * (theta * R) + theta ^ 2 * R + L / theta := by
    field_simp [ne_of_gt htheta_pos]
    <;> ring
  have htheta_sq_R : theta ^ 2 * R ≤ L := by
    have hsq := packingTheta_sq_le_log_div hR hC
    have hmul := mul_le_mul_of_nonneg_right hsq hR0
    simpa [theta, L, div_mul_cancel₀ _ (ne_of_gt hR)] using hmul
  have htheta_R : theta * R ≤ Real.sqrt (R * L) := by
    simpa [theta, L] using packingTheta_mul_le_sqrt_mul hR hC
  have hL_theta : L / theta ≤ Real.sqrt (R * L) + L := by
    simpa [theta, L] using packingLog_div_theta_le hR hC
  have hsqrt0 := Real.sqrt_nonneg (R * L)
  have hL0 : 0 ≤ L := by simpa [L] using packingLog_nonneg hC
  rw [hrewrite] at hfirst
  unfold packingDeviation
  dsimp [L] at hfirst htheta_sq_R htheta_R hL_theta hsqrt0 hL0 ⊢
  nlinarith

end WeightedEdgeColoring.FinitePartialResamplingNumerics
