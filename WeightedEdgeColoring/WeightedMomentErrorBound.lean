import WeightedEdgeColoring.WeightedMomentEstimateReduction
import Mathlib.Tactic

/-!
# Scalar error propagation for the weighted-moment estimate

These lemmas record the final algebra after the `z,d,Z` coordinates have
been mixed.  With ordered `Z`, a first-coordinate error `delta1` costs
`K*delta1`, and a diagonal/pair-coordinate error `delta2` costs
`K^2*delta2`.  Expanding `(lambda-1)^2` then gives the exact bound used to
reach `WeightedMomentEstimateMixing`.
-/

namespace WeightedEdgeColoring.WeightedMomentErrorBound

/-- Expansion of the weighted squared error from first and second normalized
moments. -/
theorem squaredError_le_of_first_second
    {W D K f delta1 delta2 first second squaredError : ℝ}
    (hfirst : W - K * delta1 ≤ first)
    (hsecond : second ≤ W + (K / f) * D + K ^ 2 * delta2)
    (hexpand : squaredError = second - 2 * first + W) :
    squaredError ≤ (K / f) * D + K ^ 2 * delta2 + 2 * K * delta1 := by
  rw [hexpand]
  linarith

/-- The non-error diagonal correction is uniformly bounded from the palette
and harmonic-weight assumptions. -/
theorem diagonalCorrection_le
    {K f D n alpha C : ℝ}
    (hn : 0 < n) (halpha : 0 < alpha) (hC : 0 ≤ C)
    (hK : 0 ≤ K) (hD : 0 ≤ D)
    (hpalette : alpha * n ≤ f) (hKlinear : K ≤ C * n)
    (hDharmonic : D ≤ 1 / alpha) :
    (K / f) * D ≤ C / alpha ^ 2 := by
  have hf : 0 < f := (mul_pos halpha hn).trans_le hpalette
  have hratio : K / f ≤ C / alpha := by
    rw [div_le_div_iff₀ hf halpha]
    nlinarith [mul_nonneg (sub_nonneg.mpr hKlinear) halpha.le,
      mul_nonneg hC (sub_nonneg.mpr hpalette)]
  have hratio0 : 0 ≤ K / f := div_nonneg hK hf.le
  calc
    (K / f) * D ≤ (C / alpha) * (1 / alpha) :=
      mul_le_mul hratio hDharmonic hD (hratio0.trans hratio)
    _ = C / alpha ^ 2 := by field_simp

/-- Combined uniform squared-error estimate in the form needed by the
estimate-mixing interface. -/
theorem squaredError_le_uniform
    {W D K f n alpha C delta1 delta2 first second squaredError : ℝ}
    (hn : 0 < n) (halpha : 0 < alpha) (hC : 0 ≤ C)
    (hK : 0 ≤ K) (hD : 0 ≤ D)
    (hpalette : alpha * n ≤ f) (hKlinear : K ≤ C * n)
    (hDharmonic : D ≤ 1 / alpha)
    (hfirst : W - K * delta1 ≤ first)
    (hsecond : second ≤ W + (K / f) * D + K ^ 2 * delta2)
    (hexpand : squaredError = second - 2 * first + W) :
    squaredError ≤ C / alpha ^ 2 + K ^ 2 * delta2 +
      2 * K * delta1 := by
  calc
    squaredError ≤ (K / f) * D + K ^ 2 * delta2 + 2 * K * delta1 :=
      squaredError_le_of_first_second hfirst hsecond hexpand
    _ ≤ C / alpha ^ 2 + K ^ 2 * delta2 + 2 * K * delta1 := by
      have hdiag := diagonalCorrection_le hn halpha hC hK hD hpalette
        hKlinear hDharmonic
      have hsum := add_le_add_right
        (add_le_add_right hdiag (K ^ 2 * delta2)) (2 * K * delta1)
      simpa only [add_assoc, add_comm, add_left_comm] using hsum

/-- A fixed constant plus `o(n)` error terms is below `sigma*n` once an
explicit three-way budget is available.  This elementary form avoids any
hidden asymptotic interface. -/
theorem squaredError_le_sigma_mul
    {constant K n delta1 delta2 sigma : ℝ}
    (hconstant : constant ≤ sigma * n / 3)
    (hfirst : 2 * K * delta1 ≤ sigma * n / 3)
    (hsecond : K ^ 2 * delta2 ≤ sigma * n / 3) :
    constant + K ^ 2 * delta2 + 2 * K * delta1 ≤ sigma * n := by
  linarith

end WeightedEdgeColoring.WeightedMomentErrorBound
