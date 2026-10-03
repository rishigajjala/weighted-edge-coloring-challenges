import WeightedEdgeColoring.FiniteCategoricalBernstein

/-!
# Elementary scalar Chernoff inequalities for the sharp round

The probability layer already exposes its exact exponential expressions.
These lemmas put the usual centered quadratic estimates into precisely that
form.  They are independent of every graph and option-system definition.
-/

namespace WeightedEdgeColoring

/-- The negative exponential has the same quadratic remainder bound on
`[0,1]` as the positive exponential. -/
theorem exp_neg_sub_one_add_id_le_sq {x : ℝ}
    (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    Real.exp (-x) - 1 + x ≤ x ^ 2 := by
  have habs : |-x| ≤ 1 := by simpa [abs_of_nonneg hx0] using hx1
  have h := Real.abs_exp_sub_one_sub_id_le habs
  calc
    Real.exp (-x) - 1 + x = Real.exp (-x) - 1 - (-x) := by ring
    _ ≤ |Real.exp (-x) - 1 - (-x)| := le_abs_self _
    _ ≤ (-x) ^ 2 := h
    _ = x ^ 2 := by ring

/-- Centered lower-tail exponent.  If the target is `M-t`, the tilt
`t/(2M)` gives the bound `exp(-t^2/(4M))`. -/
theorem lower_chernoff_scalar_le
    (M t : ℝ) (hM : 0 < M) (ht0 : 0 ≤ t) (htM : t ≤ 2 * M) :
    Real.exp
        ((t / (2 * M)) * (M - t) +
          (Real.exp (-(t / (2 * M))) - 1) * M) ≤
      Real.exp (-(t ^ 2) / (4 * M)) := by
  let lambda : ℝ := t / (2 * M)
  have hden : 0 < 2 * M := mul_pos (by norm_num) hM
  have hlambda0 : 0 ≤ lambda := div_nonneg ht0 hden.le
  have hlambda1 : lambda ≤ 1 := by
    exact (div_le_one hden).2 htM
  have hrem := exp_neg_sub_one_add_id_le_sq hlambda0 hlambda1
  apply Real.exp_le_exp.mpr
  calc
    lambda * (M - t) + (Real.exp (-lambda) - 1) * M =
        -lambda * t + (Real.exp (-lambda) - 1 + lambda) * M := by ring
    _ ≤ -lambda * t + lambda ^ 2 * M := by
      gcongr
    _ = -(t ^ 2) / (4 * M) := by
      dsimp [lambda]
      field_simp
      ring

/-- Centered upper-tail exponent, in the matching explicit tilt. -/
theorem upper_chernoff_scalar_le
    (M t : ℝ) (hM : 0 < M) (ht0 : 0 ≤ t) (htM : t ≤ 2 * M) :
    Real.exp
        (-(t / (2 * M)) * (M + t) +
          (Real.exp (t / (2 * M)) - 1) * M) ≤
      Real.exp (-(t ^ 2) / (4 * M)) := by
  let lambda : ℝ := t / (2 * M)
  have hden : 0 < 2 * M := mul_pos (by norm_num) hM
  have hlambda0 : 0 ≤ lambda := div_nonneg ht0 hden.le
  have hlambda1 : lambda ≤ 1 := by
    exact (div_le_one hden).2 htM
  have hrem :=
    FiniteCategoricalSelection.exp_sub_one_sub_id_le_sq hlambda0 hlambda1
  apply Real.exp_le_exp.mpr
  calc
    -lambda * (M + t) + (Real.exp lambda - 1) * M =
        -lambda * t + (Real.exp lambda - 1 - lambda) * M := by ring
    _ ≤ -lambda * t + lambda ^ 2 * M := by
      gcongr
    _ = -(t ^ 2) / (4 * M) := by
      dsimp [lambda]
      field_simp
      ring

/-- Lower-tail form with a possibly larger true mean and a possibly smaller
target.  This is the form used after replacing a graph row by a convenient
scalar baseline `M`. -/
theorem lower_chernoff_scalar_of_gap
    (mean target M t : ℝ)
    (hM : 0 < M) (ht0 : 0 ≤ t) (htM : t ≤ 2 * M)
    (hmean : M ≤ mean) (htarget : target ≤ M - t) :
    Real.exp
        ((t / (2 * M)) * target +
          (Real.exp (-(t / (2 * M))) - 1) * mean) ≤
      Real.exp (-(t ^ 2) / (4 * M)) := by
  have hden : 0 < 2 * M := mul_pos (by norm_num) hM
  have hlambda0 : 0 ≤ t / (2 * M) := div_nonneg ht0 hden.le
  have hcoef : Real.exp (-(t / (2 * M))) - 1 ≤ 0 := by
    exact sub_nonpos.mpr
      (Real.exp_le_one_iff.mpr (neg_nonpos.mpr hlambda0))
  calc
    Real.exp
        ((t / (2 * M)) * target +
          (Real.exp (-(t / (2 * M))) - 1) * mean) ≤
        Real.exp
          ((t / (2 * M)) * (M - t) +
            (Real.exp (-(t / (2 * M))) - 1) * M) := by
      apply Real.exp_le_exp.mpr
      exact add_le_add
        (mul_le_mul_of_nonneg_left htarget hlambda0)
        (mul_le_mul_of_nonpos_left hmean hcoef)
    _ ≤ Real.exp (-(t ^ 2) / (4 * M)) :=
      lower_chernoff_scalar_le M t hM ht0 htM

/-- Upper-tail form with a possibly smaller true mean and a possibly larger
target. -/
theorem upper_chernoff_scalar_of_gap
    (mean target M t : ℝ)
    (hM : 0 < M) (ht0 : 0 ≤ t) (htM : t ≤ 2 * M)
    (hmean : mean ≤ M) (htarget : M + t ≤ target) :
    Real.exp
        (-(t / (2 * M)) * target +
          (Real.exp (t / (2 * M)) - 1) * mean) ≤
      Real.exp (-(t ^ 2) / (4 * M)) := by
  have hden : 0 < 2 * M := mul_pos (by norm_num) hM
  have hlambda0 : 0 ≤ t / (2 * M) := div_nonneg ht0 hden.le
  have hcoef : 0 ≤ Real.exp (t / (2 * M)) - 1 := by
    exact sub_nonneg.mpr (Real.one_le_exp hlambda0)
  calc
    Real.exp
        (-(t / (2 * M)) * target +
          (Real.exp (t / (2 * M)) - 1) * mean) ≤
        Real.exp
          (-(t / (2 * M)) * (M + t) +
            (Real.exp (t / (2 * M)) - 1) * M) := by
      apply Real.exp_le_exp.mpr
      exact add_le_add
        (mul_le_mul_of_nonpos_left htarget (neg_nonpos.mpr hlambda0))
        (mul_le_mul_of_nonneg_left hmean hcoef)
    _ ≤ Real.exp (-(t ^ 2) / (4 * M)) :=
      upper_chernoff_scalar_le M t hM ht0 htM

/-- A negative quadratic Chernoff exponent pays a row weight `exp(-z)` and
an additional product exponent `B` whenever `z+B` is no larger than the
quadratic rate. -/
theorem exp_neg_quadratic_pays
    (rate z B : ℝ) (h : z + B ≤ rate) :
    Real.exp (-rate) ≤ Real.exp (-(z + B)) := by
  exact Real.exp_le_exp.mpr (by linarith)

end WeightedEdgeColoring
