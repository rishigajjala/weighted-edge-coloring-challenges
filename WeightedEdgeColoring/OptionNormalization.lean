import Mathlib.Algebra.BigOperators.Field
import Mathlib.Data.Real.Basic
import Mathlib.Tactic

/-!
# Normalizing whole-edge options

After profile choices are fixed, the total fractional option mass `S_e` of an
edge can exceed one.  The manuscript divides all options of that edge by
`max 1 S_e`.  This file proves that the operation decreases every option,
leaves total mass `min 1 S_e`, and loses at most `|S_e - μ_e|` relative to any
target mass `μ_e ≤ 1`.
-/

open scoped BigOperators

namespace WeightedEdgeColoring
namespace OptionNormalization

universe u v

variable {Job : Type u} {Option : Type v}
  [Fintype Job] [DecidableEq Job]
  [Fintype Option] [DecidableEq Option]

/-- Total option mass belonging to one job. -/
def mass (owner : Option → Job) (X : Option → ℝ) (j : Job) : ℝ :=
  ∑ o, if owner o = j then X o else 0

/-- Divide every option by the larger of one and its job's total mass. -/
noncomputable def normalized (owner : Option → Job) (X : Option → ℝ)
    (o : Option) : ℝ :=
  X o / max 1 (mass owner X (owner o))

theorem mass_nonneg (owner : Option → Job) (X : Option → ℝ)
    (hX : ∀ o, 0 ≤ X o) (j : Job) :
    0 ≤ mass owner X j := by
  unfold mass
  exact Finset.sum_nonneg fun o _ => by
    split_ifs
    · exact hX o
    · exact le_rfl

theorem one_le_normalizingDenominator
    (owner : Option → Job) (X : Option → ℝ) (o : Option) :
    1 ≤ max 1 (mass owner X (owner o)) := le_max_left _ _

theorem normalizingDenominator_pos
    (owner : Option → Job) (X : Option → ℝ) (o : Option) :
    0 < max 1 (mass owner X (owner o)) :=
  lt_of_lt_of_le zero_lt_one (one_le_normalizingDenominator owner X o)

theorem normalized_nonneg (owner : Option → Job) (X : Option → ℝ)
    (hX : ∀ o, 0 ≤ X o) (o : Option) :
    0 ≤ normalized owner X o := by
  exact div_nonneg (hX o) (normalizingDenominator_pos owner X o).le

/-- Normalization never increases an option. -/
theorem normalized_le (owner : Option → Job) (X : Option → ℝ)
    (hX : ∀ o, 0 ≤ X o) (o : Option) :
    normalized owner X o ≤ X o := by
  unfold normalized
  have hden := one_le_normalizingDenominator owner X o
  exact (div_le_iff₀ (normalizingDenominator_pos owner X o)).mpr
    (by nlinarith [hX o])

theorem mass_normalized_eq_div_max
    (owner : Option → Job) (X : Option → ℝ) (j : Job) :
    mass owner (normalized owner X) j =
      mass owner X j / max 1 (mass owner X j) := by
  unfold mass normalized
  calc
    (∑ o, if owner o = j then
        X o / max 1 (∑ p, if owner p = owner o then X p else 0) else 0) =
        ∑ o, (if owner o = j then X o else 0) /
          max 1 (∑ p, if owner p = j then X p else 0) := by
      apply Finset.sum_congr rfl
      intro o _
      by_cases hoj : owner o = j <;> simp [hoj]
    _ = (∑ o, if owner o = j then X o else 0) /
          max 1 (∑ p, if owner p = j then X p else 0) := by
      rw [Finset.sum_div]

theorem div_max_one_eq_min_one (s : ℝ) (hs : 0 ≤ s) :
    s / max 1 s = min 1 s := by
  by_cases hs1 : s ≤ 1
  · rw [max_eq_left hs1, min_eq_right hs1]
    simp
  · have h1s : 1 ≤ s := le_of_not_ge hs1
    rw [max_eq_right h1s, min_eq_left h1s]
    have hs0 : s ≠ 0 := by linarith
    field_simp

/-- The normalized option masses of a job sum to `min 1 S`. -/
theorem mass_normalized_eq_min
    (owner : Option → Job) (X : Option → ℝ)
    (hX : ∀ o, 0 ≤ X o) (j : Job) :
    mass owner (normalized owner X) j = min 1 (mass owner X j) := by
  rw [mass_normalized_eq_div_max]
  exact div_max_one_eq_min_one _ (mass_nonneg owner X hX j)

/-- The scalar capture inequality from the manuscript. -/
theorem min_one_ge_sub_abs (S μ : ℝ) (hS : 0 ≤ S) (hμ : μ ≤ 1) :
    μ - |S - μ| ≤ min 1 S := by
  by_cases hS1 : S ≤ 1
  · rw [min_eq_right hS1]
    have habs := neg_le_abs (S - μ)
    linarith
  · rw [min_eq_left (le_of_not_ge hS1)]
    have habs : μ - |S - μ| ≤ μ := sub_le_self _ (abs_nonneg _)
    exact habs.trans hμ

/-- Weighted summed form of the capture inequality. -/
theorem weighted_capture
    {E : Type*} [Fintype E]
    (weight S μ : E → ℝ)
    (hweight : ∀ e, 0 ≤ weight e)
    (hS : ∀ e, 0 ≤ S e)
    (hμ : ∀ e, μ e ≤ 1) :
    (∑ e, weight e * μ e) -
        (∑ e, weight e * |S e - μ e|) ≤
      ∑ e, weight e * min 1 (S e) := by
  rw [← Finset.sum_sub_distrib]
  exact Finset.sum_le_sum fun e _ => by
    have h := min_one_ge_sub_abs (S e) (μ e) (hS e) (hμ e)
    nlinarith [mul_le_mul_of_nonneg_left h (hweight e)]

/-- Any nonnegative weighted load can only decrease under normalization. -/
theorem weighted_normalized_load_le
    {R : Type*} [Fintype R]
    (owner : Option → Job) (X : Option → ℝ) (use : Option → R → ℝ)
    (hX : ∀ o, 0 ≤ X o) (huse : ∀ o r, 0 ≤ use o r) (r : R) :
    (∑ o, use o r * normalized owner X o) ≤
      ∑ o, use o r * X o := by
  exact Finset.sum_le_sum fun o _ =>
    mul_le_mul_of_nonneg_left (normalized_le owner X hX o) (huse o r)

end OptionNormalization
end WeightedEdgeColoring
