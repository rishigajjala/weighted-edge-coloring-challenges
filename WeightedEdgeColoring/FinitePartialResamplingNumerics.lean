import WeightedEdgeColoring.FinitePartialResamplingExponential

/-!
# Numerical parameters for mass-sensitive categorical rounding

This file isolates the elementary real inequalities used by the
partial-resampling selector.  If every row has fractional mean at most `R`
and every source--state column has total coefficient at most `C`, we use

* `L = log (3 + 16 C)`,
* `theta = min 1 (sqrt (L / R))`, and
* `b = ((1+theta)(exp theta-1)R + L) / theta`.

The exponential hitting weights then have self-charge below one half.  The
sum of their source charges, including the factor `1/(1-S)` from the PRA
criterion, is at most `theta`.  The selected assignment therefore uses the
inflated mass `(1+theta) p`.  We also record the transparent bound

`b <= R + 4 sqrt (R L) + 4 L`.

The finite witness/PRA criterion is kept in a separate module.  Everything
here is ordinary finite-sum and real arithmetic.
-/

namespace WeightedEdgeColoring.FinitePartialResamplingNumerics

open scoped BigOperators

/-- Logarithmic scale paid for one source--state column of mass `C`. -/
noncomputable def packingLog (C : ℝ) : ℝ := Real.log (3 + 16 * C)

/-- Exponential parameter for the mass-sensitive selector. -/
noncomputable def packingTheta (R C : ℝ) : ℝ :=
  min 1 (Real.sqrt (packingLog C / R))

/-- Common row threshold used by the exponential hitting weights. -/
noncomputable def packingThreshold (R C : ℝ) : ℝ :=
  let L := packingLog C
  let theta := packingTheta R C
  ((1 + theta) * (Real.exp theta - 1) * R + L) / theta

theorem three_le_three_add_sixteen_mul {C : ℝ} (hC : 0 ≤ C) :
    3 ≤ 3 + 16 * C := by linarith

theorem packingLog_pos {C : ℝ} (hC : 0 ≤ C) :
    0 < packingLog C := by
  unfold packingLog
  have hthree : (1 : ℝ) < 3 + 16 * C := by linarith
  exact Real.log_pos hthree

theorem packingLog_nonneg {C : ℝ} (hC : 0 ≤ C) :
    0 ≤ packingLog C := (packingLog_pos hC).le

theorem exp_packingLog {C : ℝ} (hC : 0 ≤ C) :
    Real.exp (packingLog C) = 3 + 16 * C := by
  unfold packingLog
  rw [Real.exp_log]
  linarith

theorem packingTheta_pos {R C : ℝ} (hR : 0 < R) (hC : 0 ≤ C) :
    0 < packingTheta R C := by
  unfold packingTheta
  apply lt_min (by norm_num)
  apply Real.sqrt_pos.2
  exact div_pos (packingLog_pos hC) hR

theorem packingTheta_nonneg {R C : ℝ} (hR : 0 < R) (hC : 0 ≤ C) :
    0 ≤ packingTheta R C := (packingTheta_pos hR hC).le

theorem packingTheta_le_one (R C : ℝ) : packingTheta R C ≤ 1 := by
  unfold packingTheta
  exact min_le_left _ _

theorem packingTheta_sq_le_log_div {R C : ℝ} (hR : 0 < R)
    (hC : 0 ≤ C) :
    (packingTheta R C) ^ 2 ≤ packingLog C / R := by
  have hsqrt0 : 0 ≤ Real.sqrt (packingLog C / R) := Real.sqrt_nonneg _
  have htheta0 := packingTheta_nonneg hR hC
  have htheta : packingTheta R C ≤ Real.sqrt (packingLog C / R) := by
    unfold packingTheta
    exact min_le_right _ _
  calc
    packingTheta R C ^ 2 ≤ (Real.sqrt (packingLog C / R)) ^ 2 := by
      nlinarith
    _ = packingLog C / R := by
      rw [Real.sq_sqrt]
      exact div_nonneg (packingLog_nonneg hC) hR.le

/-- On the chosen range, the exponential kernel is at most
`theta + theta^2`. -/
theorem exp_packingTheta_sub_one_le {R C : ℝ} (hR : 0 < R)
    (hC : 0 ≤ C) :
    Real.exp (packingTheta R C) - 1 ≤
      packingTheta R C + packingTheta R C ^ 2 := by
  have h := WeightedEdgeColoring.FiniteCategoricalSelection.exp_sub_one_sub_id_le_sq
    (packingTheta_nonneg hR hC) (packingTheta_le_one R C)
  linarith

/-- A coarser bound used for the source-charge sum. -/
theorem exp_packingTheta_sub_one_le_two_mul {R C : ℝ} (hR : 0 < R)
    (hC : 0 ≤ C) :
    Real.exp (packingTheta R C) - 1 ≤ 2 * packingTheta R C := by
  have hsq : packingTheta R C ^ 2 ≤ packingTheta R C := by
    have h0 := packingTheta_nonneg hR hC
    have h1 := packingTheta_le_one R C
    nlinarith
  linarith [exp_packingTheta_sub_one_le hR hC]

/-- The additive scale in the final row bound. -/
noncomputable def packingDeviation (R C : ℝ) : ℝ :=
  4 * Real.sqrt (R * packingLog C) + 4 * packingLog C

end WeightedEdgeColoring.FinitePartialResamplingNumerics
