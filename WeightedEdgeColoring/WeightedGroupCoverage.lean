import Mathlib

/-!
# Turning group counts into covered weight

When all jobs in a group have weights within one multiplicative factor,
covering a fixed fraction of the jobs covers nearly the same fraction of the
group's total weight.  These deterministic lemmas are the final conversion
needed after the job-group Harris rows.
-/

namespace WeightedEdgeColoring

open scoped BigOperators

universe u

variable {Job : Type u} [Fintype Job] [DecidableEq Job]

theorem card_mul_lowerWeight_le_sum
    (weight : Job → ℝ) (S : Finset Job) (a : ℝ)
    (hlower : ∀ j ∈ S, a ≤ weight j) :
    a * (S.card : ℝ) ≤ ∑ j ∈ S, weight j := by
  calc
    a * (S.card : ℝ) = ∑ _j ∈ S, a := by simp [mul_comm]
    _ ≤ ∑ j ∈ S, weight j := Finset.sum_le_sum hlower

theorem sum_le_card_mul_upperWeight
    (weight : Job → ℝ) (S : Finset Job) (b : ℝ)
    (hupper : ∀ j ∈ S, weight j ≤ b) :
    (∑ j ∈ S, weight j) ≤ b * (S.card : ℝ) := by
  calc
    (∑ j ∈ S, weight j) ≤ ∑ _j ∈ S, b := Finset.sum_le_sum hupper
    _ = b * (S.card : ℝ) := by simp [mul_comm]

/-- If every group weight lies in `[a, kappa*a]` and `covered` contains at
least a `theta` fraction of the jobs in `group`, then it contains at least a
`theta/kappa` fraction of the group's total weight. -/
theorem mul_sum_le_sum_of_nearEqual_and_card
    (weight : Job → ℝ) (group covered : Finset Job)
    (a kappa theta : ℝ)
    (ha0 : 0 ≤ a) (hkappa : 0 < kappa) (htheta0 : 0 ≤ theta)
    (hlower : ∀ j ∈ covered, a ≤ weight j)
    (hupper : ∀ j ∈ group, weight j ≤ kappa * a)
    (hcount : theta * (group.card : ℝ) ≤ (covered.card : ℝ)) :
    (theta / kappa) * (∑ j ∈ group, weight j) ≤
      ∑ j ∈ covered, weight j := by
  have hratio0 : 0 ≤ theta / kappa := div_nonneg htheta0 hkappa.le
  have hgroup := sum_le_card_mul_upperWeight weight group (kappa * a) hupper
  have hcovered := card_mul_lowerWeight_le_sum weight covered a hlower
  calc
    (theta / kappa) * (∑ j ∈ group, weight j) ≤
        (theta / kappa) * ((kappa * a) * (group.card : ℝ)) :=
      mul_le_mul_of_nonneg_left hgroup hratio0
    _ = a * (theta * (group.card : ℝ)) := by
      field_simp
    _ ≤ a * (covered.card : ℝ) :=
      mul_le_mul_of_nonneg_left hcount ha0
    _ ≤ ∑ j ∈ covered, weight j := hcovered

/-- Convenient strict-count version of the preceding conversion. -/
theorem mul_sum_lt_sum_of_nearEqual_and_card
    (weight : Job → ℝ) (group covered : Finset Job)
    (a kappa theta : ℝ)
    (ha : 0 < a) (hkappa : 0 < kappa) (htheta0 : 0 ≤ theta)
    (hlower : ∀ j ∈ covered, a ≤ weight j)
    (hupper : ∀ j ∈ group, weight j ≤ kappa * a)
    (hcount : theta * (group.card : ℝ) < (covered.card : ℝ)) :
    (theta / kappa) * (∑ j ∈ group, weight j) <
      ∑ j ∈ covered, weight j := by
  have hratio0 : 0 ≤ theta / kappa := div_nonneg htheta0 hkappa.le
  have hgroup := sum_le_card_mul_upperWeight weight group (kappa * a) hupper
  have hcovered := card_mul_lowerWeight_le_sum weight covered a hlower
  calc
    (theta / kappa) * (∑ j ∈ group, weight j) ≤
        (theta / kappa) * ((kappa * a) * (group.card : ℝ)) :=
      mul_le_mul_of_nonneg_left hgroup hratio0
    _ = a * (theta * (group.card : ℝ)) := by
      field_simp
    _ < a * (covered.card : ℝ) := by
      exact mul_lt_mul_of_pos_left hcount ha
    _ ≤ ∑ j ∈ covered, weight j := hcovered

end WeightedEdgeColoring
