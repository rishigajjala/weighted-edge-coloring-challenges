import Mathlib.Algebra.Order.Ring.Pow
import Mathlib.Tactic

/-!
# The scalar balance needed by a fixed-slack rank-three nibble

This file contains no probabilistic or graph-theoretic assertion.  It records
the first-order degree factors that a balanced rank-three nibble must deliver.

With proposal rate `a / d`, a surviving job loses options through the two
slot hazards, while an unused slot loses options through the owner hazard and
the other-slot hazard.  If the current slot/job ratio is at most `1 - gamma`,
the corresponding ideal retention factors are

`rJob = 1 - 2 * a * (1 - gamma)` and
`rSlot = 1 - a * (2 - gamma)`.

Their first-order terms cancel exactly in the gap calculation.  Consequently
an additive error `xi * d` on each side still leaves half the original gap
when `4 * xi <= gamma`.  Constructing a partial matching with these two
retention estimates is the remaining probabilistic input.
-/

namespace WeightedEdgeColoring

/-- Ideal lower retention factor for an uncovered job fibre. -/
def fixedSlackJobRetention (a gamma : ℝ) : ℝ :=
  1 - 2 * a * (1 - gamma)

/-- Ideal upper retention factor for an unused slot fibre. -/
def fixedSlackSlotRetention (a gamma : ℝ) : ℝ :=
  1 - a * (2 - gamma)

/-- The natural job and slot factors preserve exactly half of a declared
slot/job gap.  The proposal-rate terms cancel identically. -/
theorem fixedSlack_retention_exact_gap (a gamma : ℝ) :
    (1 - gamma / 2) * fixedSlackJobRetention a gamma -
        (1 - gamma) * fixedSlackSlotRetention a gamma =
      gamma / 2 := by
  simp only [fixedSlackJobRetention, fixedSlackSlotRetention]
  ring

/-- Robust form of `fixedSlack_retention_exact_gap`.

Suppose the current slot cap is `(1-gamma) * d`.  If the next surviving job
degree is at least `(rJob-xi) * d` and the next slot cap is at most
`rSlot * (1-gamma) * d + xi * d`, then the latter is at most
`(1-gamma/2)` times the former whenever `4*xi <= gamma`.

The theorem is stated before multiplying by `d`; this is the exact scalar
inequality needed by an integer-rounded recurrence. -/
theorem fixedSlack_retention_gap_with_error
    (a gamma xi : ℝ)
    (hgamma0 : 0 ≤ gamma)
    (hxi0 : 0 ≤ xi) (hxi : 4 * xi ≤ gamma) :
    fixedSlackSlotRetention a gamma * (1 - gamma) + xi ≤
      (1 - gamma / 2) * (fixedSlackJobRetention a gamma - xi) := by
  have hcoef2 : 2 - gamma / 2 ≤ 2 := by linarith
  have herror : xi * (2 - gamma / 2) ≤ gamma / 2 := by
    calc
      xi * (2 - gamma / 2) ≤ xi * 2 :=
        mul_le_mul_of_nonneg_left hcoef2 hxi0
      _ ≤ gamma / 2 := by linarith
  have hid :
      (1 - gamma / 2) * (fixedSlackJobRetention a gamma - xi) -
          (fixedSlackSlotRetention a gamma * (1 - gamma) + xi) =
        gamma / 2 - xi * (2 - gamma / 2) := by
    simp only [fixedSlackJobRetention, fixedSlackSlotRetention]
    ring
  apply sub_nonneg.mp
  rw [hid]
  linarith

end WeightedEdgeColoring
