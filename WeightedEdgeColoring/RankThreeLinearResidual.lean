import WeightedEdgeColoring.RankThreeResidualNibble
import WeightedEdgeColoring.QuantizedOptions

/-!
# Linear upper bounds for one-round residual losses

When a retained set is forced to be a partial matching by pair bad events,
the residual degree losses no longer need a nonlinear isolation estimate.
For an uncovered job, every deleted option is blocked by some selected option
of a different job.  For an unused slot, every deleted option using that slot
is likewise blocked by some selected option.  Taking a union bound over the
selected options turns both losses into linear Bernoulli statistics.
-/

namespace WeightedEdgeColoring.RankThreeOptionSystem

open scoped BigOperators

universe u v w

variable {Job : Type u} {Slot : Type v} {Option : Type w}
  [Fintype Job] [Fintype Slot] [Fintype Option]
  [DecidableEq Job] [DecidableEq Slot] [DecidableEq Option]
  (H : RankThreeOptionSystem Job Slot Option)

/-- Options of `j` blocked through slots by an option of a different job. -/
def externalBlockedBy (j : Job) (p : Option) : Finset Option :=
  if H.owner p = j then ∅ else H.blockedBy j p

/-- The linear overcount of options of `j` deleted by `A`. -/
def externalJobDeletionLoad (A : Finset Option) (j : Job) : ℕ :=
  ∑ p ∈ A, (H.externalBlockedBy j p).card

/-- Options using `s` that fail either the owner or compatibility test against
one selected option `p`. -/
def slotBlockedBy (s : Slot) (p : Option) : Finset Option :=
  ((Finset.univ : Finset Option).filter fun o ↦ s ∈ H.slots o).filter
    fun o ↦ H.owner o = H.owner p ∨ ¬ H.Compatible o p

/-- The linear overcount of options using `s` deleted by `A`. -/
def slotDeletionLoad (A : Finset Option) (s : Slot) : ℕ :=
  ∑ p ∈ A, (H.slotBlockedBy s p).card

/-- If `A` does not cover `j`, every option of `j` removed from the empty
residual system is counted by at least one external blocker in `A`. -/
theorem removedResidualFiber_empty_subset_externalBlockers
    (A : Finset Option) (j : Job) (huncovered : ¬ H.Covers A j) :
    H.removedResidualFiber ∅ A j ⊆
      A.biUnion (H.externalBlockedBy j) := by
  intro o ho
  have hbase : o ∈ H.residualFiber ∅ j := (Finset.mem_sdiff.mp ho).1
  have hnot : o ∉ H.residualFiber (∅ ∪ A) j := (Finset.mem_sdiff.mp ho).2
  have howner : H.owner o = j := (H.mem_residualFiber.mp hbase).1
  have hfail : ¬ ∀ p ∈ A,
      H.owner o ≠ H.owner p ∧ H.Compatible o p := by
    intro hall
    apply hnot
    apply H.mem_residualFiber.mpr
    simpa using And.intro howner hall
  push Not at hfail
  rcases hfail with ⟨p, hpA, hfailp⟩
  have hpowner : H.owner p ≠ j := by
    intro hpj
    exact huncovered ⟨p, hpA, hpj⟩
  have hone : H.owner o ≠ H.owner p := by
    simpa [howner] using hpowner.symm
  have hincompat : ¬ H.Compatible o p := by
    exact hfailp hone
  apply Finset.mem_biUnion.mpr
  refine ⟨p, hpA, ?_⟩
  simp [externalBlockedBy, hpowner, H.mem_blockedBy, howner, hincompat]

/-- Consequently, the residual job-degree loss of every uncovered job is at
most a linear sum over the selected options. -/
theorem removedResidualFiber_empty_card_le_externalJobDeletionLoad
    (A : Finset Option) (j : Job) (huncovered : ¬ H.Covers A j) :
    (H.removedResidualFiber ∅ A j).card ≤
      H.externalJobDeletionLoad A j := by
  calc
    (H.removedResidualFiber ∅ A j).card ≤
        (A.biUnion (H.externalBlockedBy j)).card :=
      Finset.card_le_card
        (H.removedResidualFiber_empty_subset_externalBlockers A j huncovered)
    _ ≤ ∑ p ∈ A, (H.externalBlockedBy j p).card :=
      Finset.card_biUnion_le
    _ = H.externalJobDeletionLoad A j := rfl

/-- If no selected option uses `s`, every removed residual option using `s`
is counted by one of the linear slot blockers. -/
theorem removedResidualSlot_empty_subset_slotBlockers
    (A : Finset Option) (s : Slot)
    (hunused : ∀ p ∈ A, s ∉ H.slots p) :
    H.removedResidualSlot ∅ A s ⊆ A.biUnion (H.slotBlockedBy s) := by
  intro o ho
  have hbase := (Finset.mem_sdiff.mp ho).1
  have hnot := (Finset.mem_sdiff.mp ho).2
  have hos : s ∈ H.slots o := (Finset.mem_filter.mp hbase).2
  have hoUniv : o ∈ H.residualOptions ∅ := (Finset.mem_filter.mp hbase).1
  have hfail : ¬ ∀ p ∈ A,
      H.owner o ≠ H.owner p ∧ H.Compatible o p := by
    intro hall
    apply hnot
    apply Finset.mem_filter.mpr
    refine ⟨?_, hos⟩
    rw [H.mem_residualOptions]
    simpa using hall
  push Not at hfail
  rcases hfail with ⟨p, hpA, hfailp⟩
  have hbad : H.owner o = H.owner p ∨ ¬ H.Compatible o p := by
    by_cases heq : H.owner o = H.owner p
    · exact Or.inl heq
    · exact Or.inr (hfailp heq)
  apply Finset.mem_biUnion.mpr
  refine ⟨p, hpA, ?_⟩
  simp [slotBlockedBy, hos, hbad]

/-- Linear cardinality bound for the loss at an unused slot. -/
theorem removedResidualSlot_empty_card_le_slotDeletionLoad
    (A : Finset Option) (s : Slot)
    (hunused : ∀ p ∈ A, s ∉ H.slots p) :
    (H.removedResidualSlot ∅ A s).card ≤ H.slotDeletionLoad A s := by
  calc
    (H.removedResidualSlot ∅ A s).card ≤
        (A.biUnion (H.slotBlockedBy s)).card :=
      Finset.card_le_card
        (H.removedResidualSlot_empty_subset_slotBlockers A s hunused)
    _ ≤ ∑ p ∈ A, (H.slotBlockedBy s p).card :=
      Finset.card_biUnion_le
    _ = H.slotDeletionLoad A s := rfl

/-- One external option blocks at most `2*lambda` options of a fixed job. -/
theorem externalBlockedBy_card_le_two_mul
    (j : Job) (p : Option) (lambda : ℕ)
    (hcodeg : ∀ t ∈ H.slots p, H.jobSlotCodegree j t ≤ lambda) :
    (H.externalBlockedBy j p).card ≤ 2 * lambda := by
  by_cases hpj : H.owner p = j
  · simp [externalBlockedBy, hpj]
  · simp only [externalBlockedBy, hpj, if_false]
    exact H.card_blockedBy_le_two_mul j p lambda hcodeg

/-- Same-owner options using `s`. -/
def ownerSlotFiber (p : Option) (s : Slot) : Finset Option :=
  (H.fiber (H.owner p)).filter fun o ↦ s ∈ H.slots o

/-- Options simultaneously using two specified slots. -/
def slotPairFiber (s t : Slot) : Finset Option :=
  (Finset.univ : Finset Option).filter fun o ↦
    s ∈ H.slots o ∧ t ∈ H.slots o

theorem ownerSlotFiber_card (p : Option) (s : Slot) :
    (H.ownerSlotFiber p s).card = H.jobSlotCodegree (H.owner p) s := by
  rfl

theorem slotPairFiber_card (s t : Slot) :
    (H.slotPairFiber s t).card = H.slotPairCodegree s t := by
  rfl

/-- A slot blocker is contained in the same-owner part together with one
slot-pair part for each slot of the selected option. -/
theorem slotBlockedBy_subset_owner_union_pairs (s : Slot) (p : Option) :
    H.slotBlockedBy s p ⊆
      H.ownerSlotFiber p s ∪
        (H.slots p).biUnion (H.slotPairFiber s) := by
  intro o ho
  have hmem := Finset.mem_filter.mp ho
  have hos : s ∈ H.slots o := (Finset.mem_filter.mp hmem.1).2
  rcases hmem.2 with howner | hconflict
  · apply Finset.mem_union_left
    simp [ownerSlotFiber, H.mem_fiber, howner, hos]
  · apply Finset.mem_union_right
    rw [Compatible, Finset.not_disjoint_iff] at hconflict
    rcases hconflict with ⟨t, hot, hpt⟩
    exact Finset.mem_biUnion.mpr ⟨t, hpt,
      Finset.mem_filter.mpr ⟨Finset.mem_univ o, hos, hot⟩⟩

/-- Under job-slot and distinct slot-pair codegree `lambda`, an option not
using `s` deletes at most `3*lambda` options incident with `s`. -/
theorem slotBlockedBy_card_le_three_mul
    (s : Slot) (p : Option) (lambda : ℕ)
    (hsp : s ∉ H.slots p)
    (hjob : H.jobSlotCodegree (H.owner p) s ≤ lambda)
    (hpair : ∀ t ∈ H.slots p, s ≠ t →
      H.slotPairCodegree s t ≤ lambda) :
    (H.slotBlockedBy s p).card ≤ 3 * lambda := by
  calc
    (H.slotBlockedBy s p).card ≤
        (H.ownerSlotFiber p s ∪
          (H.slots p).biUnion (H.slotPairFiber s)).card :=
      Finset.card_le_card (H.slotBlockedBy_subset_owner_union_pairs s p)
    _ ≤ (H.ownerSlotFiber p s).card +
        ((H.slots p).biUnion (H.slotPairFiber s)).card :=
      Finset.card_union_le _ _
    _ ≤ (H.ownerSlotFiber p s).card +
        ∑ t ∈ H.slots p, (H.slotPairFiber s t).card := by
      gcongr
      exact Finset.card_biUnion_le
    _ ≤ lambda + ∑ _t ∈ H.slots p, lambda := by
      rw [H.ownerSlotFiber_card]
      apply Nat.add_le_add hjob
      exact Finset.sum_le_sum fun t ht ↦ by
        rw [H.slotPairFiber_card]
        apply hpair t ht
        intro hst
        apply hsp
        simpa [hst] using ht
    _ = lambda + (H.slots p).card * lambda := by simp
    _ ≤ lambda + 2 * lambda := by
      gcongr
      exact H.slots_card_le_two p
    _ = 3 * lambda := by omega

end WeightedEdgeColoring.RankThreeOptionSystem
