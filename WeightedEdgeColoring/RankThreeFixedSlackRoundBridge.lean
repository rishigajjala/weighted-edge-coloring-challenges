import WeightedEdgeColoring.RankThreeFixedSlackBalance
import WeightedEdgeColoring.RankThreeResidualCollision

/-!
# Deterministic bridge for a balanced fixed-slack round

This file isolates the exact deterministic conclusion needed after a direct
nibble.  The job side only needs an upper bound on genuine deletion.  The
slot side needs a lower bound on the linear blocker load together with an
additive bound on its collision deficit.  The exact collision identity then
recovers the desired first-order slot retention, without the factor-two loss
of the coarse multiplicity argument.

The probabilistic construction of a partial matching satisfying the three
displayed bounds is deliberately not asserted here.  In particular, bounded
job/slot/codegrees alone do not imply the required slot-load lower bound:
the second slot of an option may have arbitrarily small degree.
-/

namespace WeightedEdgeColoring.RankThreeOptionSystem

universe u v w

variable {Job : Type u} {Slot : Type v} {Option : Type w}
  [Fintype Job] [Fintype Slot] [Fintype Option]
  [DecidableEq Job] [DecidableEq Slot] [DecidableEq Option]
  (H : RankThreeOptionSystem Job Slot Option)

/-- Exact fixed-slack balance from the three statistics that a balanced
direct nibble has to control.

The lower slot-load hypothesis contains both first-order hazards: the owner
hazard and the other-slot hazard.  The collision hypothesis charges only the
quadratic overcount in that linear statistic. -/
theorem fixedSlack_balance_of_jobLoss_slotLoad_collision
    (A : Finset Option) (d : ℕ) (a gamma xi : ℝ)
    (hjobInitial : ∀ j, d ≤ H.residualJobDegree ∅ j)
    (hjobLoss : ∀ j, ¬ H.Covers A j →
      ((H.removedResidualFiber ∅ A j).card : ℝ) ≤
        (2 * a * (1 - gamma) + xi) * d)
    (hslotInitial : ∀ s,
      (H.residualSlotDegree ∅ s : ℝ) ≤ (1 - gamma) * d)
    (hslotLoad : ∀ s, (∀ p ∈ A, s ∉ H.slots p) →
      a * (2 - gamma) * (1 - gamma) * d ≤
        (H.slotDeletionLoad A s : ℝ))
    (hslotCollision : ∀ s, (∀ p ∈ A, s ∉ H.slots p) →
      (WeightedEdgeColoring.collisionDeficit A (H.slotBlockedBy s) : ℝ) ≤ xi * d) :
    (∀ j, ¬ H.Covers A j →
      (WeightedEdgeColoring.fixedSlackJobRetention a gamma - xi) * d ≤
        H.residualJobDegree A j) ∧
    (∀ s, (∀ p ∈ A, s ∉ H.slots p) →
      (H.residualSlotDegree A s : ℝ) ≤
        (WeightedEdgeColoring.fixedSlackSlotRetention a gamma * (1 - gamma) + xi) * d) := by
  constructor
  · intro j huncovered
    have hid := H.residualJobDegree_union_add_removed ∅ A j
    simp only [Finset.empty_union] at hid
    have hidReal :
        (H.residualJobDegree A j : ℝ) +
            (H.removedResidualFiber ∅ A j).card =
          H.residualJobDegree ∅ j := by
      exact_mod_cast hid
    have hinitial : (d : ℝ) ≤ H.residualJobDegree ∅ j := by
      exact_mod_cast hjobInitial j
    have hloss := hjobLoss j huncovered
    rw [WeightedEdgeColoring.fixedSlackJobRetention]
    push_cast
    nlinarith
  · intro s hunused
    have hdelete := H.slotDeletionLoad_eq_removed_add_collisionDeficit
      A s hunused
    have hdeleteReal :
        (H.slotDeletionLoad A s : ℝ) =
          (H.removedResidualSlot ∅ A s).card +
            WeightedEdgeColoring.collisionDeficit A (H.slotBlockedBy s) := by
      exact_mod_cast hdelete
    have hid := H.residualSlotDegree_union_add_removed ∅ A s
    simp only [Finset.empty_union] at hid
    have hidReal :
        (H.residualSlotDegree A s : ℝ) +
            (H.removedResidualSlot ∅ A s).card =
          H.residualSlotDegree ∅ s := by
      exact_mod_cast hid
    have hinitial := hslotInitial s
    have hload := hslotLoad s hunused
    have hcollision := hslotCollision s hunused
    rw [WeightedEdgeColoring.fixedSlackSlotRetention]
    push_cast
    nlinarith

end WeightedEdgeColoring.RankThreeOptionSystem
