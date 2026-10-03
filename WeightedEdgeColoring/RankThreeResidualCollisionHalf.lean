import WeightedEdgeColoring.RankThreeResidualCollision

/-!
# A factor-two conversion from linear deletion load to real deletion

For a partial matching, an option in an uncovered job row or an unused slot
row has at most two selected blockers.  Therefore the linear blocker count is
at most twice the number of distinct options actually deleted.  This turns a
lower bound on the linear statistic into a lower bound on genuine residual
degree loss without a separate collision concentration estimate.
-/

namespace WeightedEdgeColoring

open scoped BigOperators

section Generic

universe u v

variable {α : Type u} {β : Type v}
  [Fintype α] [DecidableEq α] [Fintype β] [DecidableEq β]

/-- If every element of the union is counted at most twice, the sum of the
set sizes is at most twice the union size. -/
theorem sum_card_le_two_mul_card_biUnion_of_multiplicity_le_two
    (A : Finset α) (F : α → Finset β)
    (hmult : ∀ x ∈ A.biUnion F, blockerMultiplicity A F x ≤ 2) :
    (∑ a ∈ A, (F a).card) ≤ 2 * (A.biUnion F).card := by
  rw [sum_card_eq_card_biUnion_add_collisionDeficit]
  have hcollision : collisionDeficit A F ≤ (A.biUnion F).card := by
    unfold collisionDeficit
    calc
      (∑ x ∈ A.biUnion F, (blockerMultiplicity A F x - 1)) ≤
          ∑ _x ∈ A.biUnion F, 1 := by
        apply Finset.sum_le_sum
        intro x hx
        have hx' := hmult x hx
        omega
      _ = (A.biUnion F).card := by simp
  omega

end Generic

namespace RankThreeOptionSystem

universe u v w

variable {Job : Type u} {Slot : Type v} {Option : Type w}
  [Fintype Job] [Fintype Slot] [Fintype Option]
  [DecidableEq Job] [DecidableEq Slot] [DecidableEq Option]
  (H : RankThreeOptionSystem Job Slot Option)

/-- On an uncovered job row, the linear external-blocker load is at most
twice the number of options genuinely removed. -/
theorem externalJobDeletionLoad_le_two_mul_removed
    (A : Finset Option) (j : Job) (hA : H.IsPartialMatching A)
    (huncovered : ¬ H.Covers A j) :
    H.externalJobDeletionLoad A j ≤
      2 * (H.removedResidualFiber ∅ A j).card := by
  rw [externalJobDeletionLoad]
  calc
    (∑ p ∈ A, (H.externalBlockedBy j p).card) ≤
        2 * (A.biUnion (H.externalBlockedBy j)).card :=
      sum_card_le_two_mul_card_biUnion_of_multiplicity_le_two
        A (H.externalBlockedBy j)
        (fun o _ ↦ H.externalBlockerMultiplicity_le_two A j o hA)
    _ = 2 * (H.removedResidualFiber ∅ A j).card := by
      rw [H.removedResidualFiber_empty_eq_externalBlockers A j huncovered]

/-- At an unused slot, the linear slot-blocker load is at most twice the
number of options genuinely removed from that slot. -/
theorem slotDeletionLoad_le_two_mul_removed
    (A : Finset Option) (s : Slot) (hA : H.IsPartialMatching A)
    (hunused : ∀ p ∈ A, s ∉ H.slots p) :
    H.slotDeletionLoad A s ≤
      2 * (H.removedResidualSlot ∅ A s).card := by
  rw [slotDeletionLoad]
  calc
    (∑ p ∈ A, (H.slotBlockedBy s p).card) ≤
        2 * (A.biUnion (H.slotBlockedBy s)).card :=
      sum_card_le_two_mul_card_biUnion_of_multiplicity_le_two
        A (H.slotBlockedBy s)
        (fun o _ ↦ H.slotBlockerMultiplicity_le_two A s o hA hunused)
    _ = 2 * (H.removedResidualSlot ∅ A s).card := by
      rw [H.removedResidualSlot_empty_eq_slotBlockers A s hunused]

/-- A lower bound on linear job deletion gives half as much genuine degree
loss. -/
theorem job_linear_deletion_lower_le_two_mul_degree_loss
    (A : Finset Option) (j : Job) (hA : H.IsPartialMatching A)
    (huncovered : ¬ H.Covers A j) (L : ℕ)
    (hL : L ≤ H.externalJobDeletionLoad A j) :
    L ≤ 2 * (H.removedResidualFiber ∅ A j).card :=
  hL.trans (H.externalJobDeletionLoad_le_two_mul_removed
    A j hA huncovered)

/-- A lower bound on linear slot deletion gives half as much genuine degree
loss. -/
theorem slot_linear_deletion_lower_le_two_mul_degree_loss
    (A : Finset Option) (s : Slot) (hA : H.IsPartialMatching A)
    (hunused : ∀ p ∈ A, s ∉ H.slots p) (L : ℕ)
    (hL : L ≤ H.slotDeletionLoad A s) :
    L ≤ 2 * (H.removedResidualSlot ∅ A s).card :=
  hL.trans (H.slotDeletionLoad_le_two_mul_removed
    A s hA hunused)

/-- The same job-row conclusion written directly as an upper bound on the
new residual degree. -/
theorem two_mul_residualJobDegree_add_linearLower_le
    (A : Finset Option) (j : Job) (hA : H.IsPartialMatching A)
    (huncovered : ¬ H.Covers A j) (L : ℕ)
    (hL : L ≤ H.externalJobDeletionLoad A j) :
    2 * H.residualJobDegree A j + L ≤
      2 * H.residualJobDegree ∅ j := by
  have hloss := H.job_linear_deletion_lower_le_two_mul_degree_loss
    A j hA huncovered L hL
  have hid := H.residualJobDegree_union_add_removed ∅ A j
  simp only [Finset.empty_union] at hid
  omega

/-- The same slot-row conclusion written directly as an upper bound on the
new residual slot degree. -/
theorem two_mul_residualSlotDegree_add_linearLower_le
    (A : Finset Option) (s : Slot) (hA : H.IsPartialMatching A)
    (hunused : ∀ p ∈ A, s ∉ H.slots p) (L : ℕ)
    (hL : L ≤ H.slotDeletionLoad A s) :
    2 * H.residualSlotDegree A s + L ≤
      2 * H.residualSlotDegree ∅ s := by
  have hloss := H.slot_linear_deletion_lower_le_two_mul_degree_loss
    A s hA hunused L hL
  have hid := H.residualSlotDegree_union_add_removed ∅ A s
  simp only [Finset.empty_union] at hid
  omega

end RankThreeOptionSystem

end WeightedEdgeColoring
