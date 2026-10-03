import WeightedEdgeColoring.OptionNormalization
import Mathlib.Tactic

/-!
# Quadratic control of whole-edge clipping

The whole-edge construction first produces a nonnegative total option mass
`S_e` for each edge and then clips it to `min 1 S_e`.  Absolute-deviation
control is sufficient for this step, but it is stronger than necessary.  If
the target mass `mu_e` stays a fixed distance `kappa` below one, the loss from
clipping is bounded by a square.  This lets the profile-selection argument
track additive first and second moments instead of absolute values.

Everything in this file is a deterministic finite inequality.  No
probabilistic or asymptotic input is hidden in the statements.
-/

open scoped BigOperators

namespace WeightedEdgeColoring
namespace OptionNormalization

universe u v

/-- Quadratic clipping inequality.  A target at distance at least `kappa`
below one pays for every amount by which `S` is clipped. -/
theorem min_one_ge_sub_sq_div
    (S mu kappa : ℝ) (hkappa : 0 < kappa)
    (hmu : mu ≤ 1 - kappa) :
    S - (S - mu) ^ 2 / (4 * kappa) ≤ min 1 S := by
  have hden : 0 < 4 * kappa := mul_pos (by norm_num) hkappa
  by_cases hS : S ≤ 1
  · rw [min_eq_right hS]
    exact sub_le_self S (div_nonneg (sq_nonneg (S - mu)) hden.le)
  · have hx : 0 ≤ S - 1 := sub_nonneg.mpr (le_of_not_ge hS)
    have ha : kappa ≤ 1 - mu := by linarith
    have hxa : kappa * (S - 1) ≤ (1 - mu) * (S - 1) := by
      exact mul_le_mul_of_nonneg_right ha hx
    have hamgm : 4 * ((1 - mu) * (S - 1)) ≤ (S - mu) ^ 2 := by
      nlinarith [sq_nonneg ((S - 1) - (1 - mu))]
    have hpay : 4 * kappa * (S - 1) ≤ (S - mu) ^ 2 := by
      nlinarith
    rw [min_eq_left (le_of_not_ge hS)]
    have hdiv : S - 1 ≤ (S - mu) ^ 2 / (4 * kappa) := by
      apply (le_div_iff₀ hden).2
      nlinarith
    linarith

/-- Pointwise quadratic clipping, summed with arbitrary nonnegative weights. -/
theorem weighted_quadratic_clipping
    {E : Type u} [Fintype E]
    (weight S mu : E → ℝ) (kappa : ℝ)
    (hweight : ∀ e, 0 ≤ weight e)
    (hkappa : 0 < kappa)
    (hmu : ∀ e, mu e ≤ 1 - kappa) :
    (∑ e, weight e *
      (S e - (S e - mu e) ^ 2 / (4 * kappa))) ≤
      ∑ e, weight e * min 1 (S e) := by
  exact Finset.sum_le_sum fun e _he =>
    mul_le_mul_of_nonneg_left
      (min_one_ge_sub_sq_div (S e) (mu e) kappa hkappa (hmu e))
      (hweight e)

/-- Expanded form of `weighted_quadratic_clipping`: total clipped mass is at
least the uncut first moment minus `1/(4*kappa)` times the quadratic error. -/
theorem weighted_quadratic_capture
    {E : Type u} [Fintype E]
    (weight S mu : E → ℝ) (kappa : ℝ)
    (hweight : ∀ e, 0 ≤ weight e)
    (hkappa : 0 < kappa)
    (hmu : ∀ e, mu e ≤ 1 - kappa) :
    (∑ e, weight e * S e) -
        (∑ e, weight e * (S e - mu e) ^ 2) / (4 * kappa) ≤
      ∑ e, weight e * min 1 (S e) := by
  have hclip := weighted_quadratic_clipping weight S mu kappa
    hweight hkappa hmu
  calc
    (∑ e, weight e * S e) -
          (∑ e, weight e * (S e - mu e) ^ 2) / (4 * kappa) =
        ∑ e, weight e *
          (S e - (S e - mu e) ^ 2 / (4 * kappa)) := by
            rw [Finset.sum_div, ← Finset.sum_sub_distrib]
            apply Finset.sum_congr rfl
            intro e _he
            ring
    _ ≤ ∑ e, weight e * min 1 (S e) := hclip

/-- The exact interface needed after profile synchronization.  A lower bound
on the weighted first moment and an upper bound on the weighted squared error
give a lower bound on the mass surviving clipping. -/
theorem weighted_quadratic_capture_of_moment_bounds
    {E : Type u} [Fintype E]
    (weight S mu : E → ℝ) (kappa firstError secondError : ℝ)
    (hweight : ∀ e, 0 ≤ weight e)
    (hkappa : 0 < kappa)
    (hmu : ∀ e, mu e ≤ 1 - kappa)
    (hfirst : (∑ e, weight e * mu e) - firstError ≤
      ∑ e, weight e * S e)
    (hsecond : (∑ e, weight e * (S e - mu e) ^ 2) ≤ secondError) :
    (∑ e, weight e * mu e) - firstError -
        secondError / (4 * kappa) ≤
      ∑ e, weight e * min 1 (S e) := by
  have hden : 0 < 4 * kappa := mul_pos (by norm_num) hkappa
  have hsecondDiv :
      (∑ e, weight e * (S e - mu e) ^ 2) / (4 * kappa) ≤
        secondError / (4 * kappa) :=
    div_le_div_of_nonneg_right hsecond hden.le
  have hclip := weighted_quadratic_capture weight S mu kappa
    hweight hkappa hmu
  linarith

/-! ## Passing the clipping estimates to actual normalized options -/

/-- The scalar quadratic clipping estimate, stated directly for the total
mass left by option normalization.  This removes the intermediate
`min 1 S` expression from later whole-edge arguments. -/
theorem mass_normalized_ge_sub_sq_div
    {Job : Type u} {Option : Type v}
    [Fintype Job] [DecidableEq Job]
    [Fintype Option] [DecidableEq Option]
    (owner : Option → Job) (X : Option → ℝ)
    (hX : ∀ o, 0 ≤ X o) (j : Job) (mu kappa : ℝ)
    (hkappa : 0 < kappa) (hmu : mu ≤ 1 - kappa) :
    mass owner X j - (mass owner X j - mu) ^ 2 / (4 * kappa) ≤
      mass owner (normalized owner X) j := by
  rw [mass_normalized_eq_min owner X hX j]
  exact min_one_ge_sub_sq_div (mass owner X j) mu kappa hkappa hmu

/-- Weighted quadratic capture for the option masses that remain after
normalizing every job. -/
theorem weighted_normalized_quadratic_capture
    {Job : Type u} {Option : Type v}
    [Fintype Job] [DecidableEq Job]
    [Fintype Option] [DecidableEq Option]
    (owner : Option → Job) (X : Option → ℝ)
    (weight mu : Job → ℝ) (kappa : ℝ)
    (hX : ∀ o, 0 ≤ X o)
    (hweight : ∀ j, 0 ≤ weight j)
    (hkappa : 0 < kappa)
    (hmu : ∀ j, mu j ≤ 1 - kappa) :
    (∑ j, weight j * mass owner X j) -
        (∑ j, weight j * (mass owner X j - mu j) ^ 2) /
          (4 * kappa) ≤
      ∑ j, weight j * mass owner (normalized owner X) j := by
  calc
    (∑ j, weight j * mass owner X j) -
          (∑ j, weight j * (mass owner X j - mu j) ^ 2) /
            (4 * kappa) ≤
        ∑ j, weight j * min 1 (mass owner X j) :=
      weighted_quadratic_capture weight (mass owner X) mu kappa
        hweight hkappa hmu
    _ = ∑ j, weight j * mass owner (normalized owner X) j := by
      apply Finset.sum_congr rfl
      intro j _hj
      rw [mass_normalized_eq_min owner X hX j]

/-- The moment-bound interface with the conclusion stated directly as
captured normalized option mass.  Once profile synchronization supplies the
two displayed hypotheses, no further clipping argument is needed. -/
theorem weighted_normalized_quadratic_capture_of_moment_bounds
    {Job : Type u} {Option : Type v}
    [Fintype Job] [DecidableEq Job]
    [Fintype Option] [DecidableEq Option]
    (owner : Option → Job) (X : Option → ℝ)
    (weight mu : Job → ℝ)
    (kappa firstError secondError : ℝ)
    (hX : ∀ o, 0 ≤ X o)
    (hweight : ∀ j, 0 ≤ weight j)
    (hkappa : 0 < kappa)
    (hmu : ∀ j, mu j ≤ 1 - kappa)
    (hfirst : (∑ j, weight j * mu j) - firstError ≤
      ∑ j, weight j * mass owner X j)
    (hsecond :
      (∑ j, weight j * (mass owner X j - mu j) ^ 2) ≤ secondError) :
    (∑ j, weight j * mu j) - firstError -
        secondError / (4 * kappa) ≤
      ∑ j, weight j * mass owner (normalized owner X) j := by
  calc
    (∑ j, weight j * mu j) - firstError -
          secondError / (4 * kappa) ≤
        ∑ j, weight j * min 1 (mass owner X j) :=
      weighted_quadratic_capture_of_moment_bounds weight (mass owner X) mu
        kappa firstError secondError hweight hkappa hmu hfirst hsecond
    _ = ∑ j, weight j * mass owner (normalized owner X) j := by
      apply Finset.sum_congr rfl
      intro j _hj
      rw [mass_normalized_eq_min owner X hX j]

/-- If a job's total option mass is already at most one, normalization does
not change any option of that job. -/
theorem normalized_eq_self_of_mass_le_one
    {Job : Type u} {Option : Type v}
    [Fintype Job] [DecidableEq Job]
    [Fintype Option] [DecidableEq Option]
    (owner : Option → Job) (X : Option → ℝ) (o : Option)
    (hmass : mass owner X (owner o) ≤ 1) :
    normalized owner X o = X o := by
  simp [normalized, max_eq_left hmass]

/-- A safeguarded job keeps a fixed amount of unused mass after clipping. -/
theorem one_sub_mass_normalized_ge_half
    {Job : Type u} {Option : Type v}
    [Fintype Job] [DecidableEq Job]
    [Fintype Option] [DecidableEq Option]
    (owner : Option → Job) (X : Option → ℝ)
    (hX : ∀ o, 0 ≤ X o) (j : Job) (kappa : ℝ)
    (hkappa : 0 ≤ kappa)
    (hsafe : mass owner X j ≤ 1 - kappa / 2) :
    kappa / 2 ≤ 1 - mass owner (normalized owner X) j := by
  rw [mass_normalized_eq_min owner X hX j]
  have hle : mass owner X j ≤ 1 := by linarith
  rw [min_eq_right hle]
  linarith

end OptionNormalization
end WeightedEdgeColoring
