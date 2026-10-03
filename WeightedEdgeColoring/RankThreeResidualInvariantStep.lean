import WeightedEdgeColoring.RankThreeResidualActiveSlotUniform
import WeightedEdgeColoring.RankThreeResidualComposition

/-!
# Deterministic persistence after one residual round

This file contains only the bookkeeping after a one-round choice.  It turns
the job and active-slot conclusions of the Harris round into lower and upper
degree invariants for the next residual system.
-/

namespace WeightedEdgeColoring.RankThreeOptionSystem

universe u v w

variable {Job : Type u} {Slot : Type v} {Option : Type w}
  [Fintype Job] [Fintype Slot] [Fintype Option]
  [DecidableEq Job] [DecidableEq Slot] [DecidableEq Option]
  (H : RankThreeOptionSystem Job Slot Option)

@[simp] theorem residualJobDegree_empty (j : Job) :
    H.residualJobDegree ∅ j = (H.fiber j).card := by
  unfold residualJobDegree residualFiber residualOptions fiber
  simp

@[simp] theorem residualSlotDegree_empty (s : Slot) :
    H.residualSlotDegree ∅ s = H.slotDegree s := by
  unfold residualSlotDegree residualOptions slotDegree
  simp

/-- Residual slot degree can only decrease. -/
theorem residualSlotDegree_le (A : Finset Option) (s : Slot) :
    H.residualSlotDegree A s ≤ H.slotDegree s := by
  unfold residualSlotDegree slotDegree
  apply Finset.card_le_card
  intro o ho
  exact Finset.mem_filter.mpr
    ⟨Finset.mem_univ _, (Finset.mem_filter.mp ho).2⟩

/-- Once a selected option uses a slot, no residual option can use it. -/
theorem residualSlotDegree_eq_zero_of_selected_uses
    (A : Finset Option) (s : Slot) {p : Option}
    (hp : p ∈ A) (hps : s ∈ H.slots p) :
    H.residualSlotDegree A s = 0 := by
  rw [residualSlotDegree, Finset.card_eq_zero]
  apply Finset.eq_empty_iff_forall_notMem.mpr
  intro o ho
  have ho' := Finset.mem_filter.mp ho
  have hres := H.mem_residualOptions.mp ho'.1 p hp
  exact (Finset.disjoint_left.mp hres.2) ho'.2 hps

/-- An upper-loss bound for every uncovered job preserves a uniform lower
degree for the owner of every option that survives to the next residual
system.  Empty job fibres are irrelevant. -/
theorem residual_owner_fiber_card_ge_sub
    (A : Finset Option) (d U : ℕ)
    (hlower : ∀ o, d ≤ (H.fiber (H.owner o)).card)
    (hjob : ∀ j, ¬ H.Covers A j →
      H.residualJobDegree ∅ j ≤ H.residualJobDegree A j + U) :
    ∀ q : H.ResidualOption A,
      d - U ≤ ((H.residualSystem A).fiber
        ((H.residualSystem A).owner q)).card := by
  intro q
  have hnot : ¬ H.Covers A (H.owner q.1) := by
    rintro ⟨p, hp, howner⟩
    have hres := H.mem_residualOptions.mp q.2 p hp
    exact hres.1 howner.symm
  rw [H.residualSystem_fiber_card]
  have hj := hjob (H.owner q.1) hnot
  rw [H.residualJobDegree_empty] at hj
  exact Nat.sub_le_iff_le_add.mpr ((hlower q.1).trans hj)

/-- The active-slot shrink conclusion gives a uniform upper bound `S'` for
the next residual system.  Inactive slots already lie below the threshold;
used slots disappear; and unused active slots pay the stated budget. -/
theorem residualSlotDegree_le_of_active_shrink
    (A : Finset Option) (threshold budget S S' : ℕ)
    (hupper : ∀ s, H.slotDegree s ≤ S)
    (hthreshold : threshold ≤ S' + 1)
    (hbudget : 2 * S ≤ 2 * S' + budget)
    (hshrink : ∀ s : H.ActiveSlot threshold,
      (∀ p ∈ A, s.1 ∉ H.slots p) →
        2 * H.residualSlotDegree A s.1 + budget ≤
          2 * H.residualSlotDegree ∅ s.1) :
    ∀ s, H.residualSlotDegree A s ≤ S' := by
  intro s
  by_cases hused : ∃ p ∈ A, s ∈ H.slots p
  · rcases hused with ⟨p, hp, hps⟩
    rw [H.residualSlotDegree_eq_zero_of_selected_uses A s hp hps]
    exact Nat.zero_le _
  · have hunused : ∀ p ∈ A, s ∉ H.slots p := by
      intro p hp hps
      exact hused ⟨p, hp, hps⟩
    by_cases hactive : threshold ≤ H.slotDegree s
    · have hs := hshrink ⟨s, hactive⟩ hunused
      have hs' :
          2 * H.residualSlotDegree A s + budget ≤
            2 * H.slotDegree s := by
        simpa only [H.residualSlotDegree_empty] using hs
      have hold := hupper s
      omega
    · have hres := H.residualSlotDegree_le A s
      omega

/-- The two preceding invariants transported from a residual round back to
the accumulated matching in the original option system. -/
theorem residual_union_degree_invariants
    (M : Finset Option) (A : Finset (H.ResidualOption M))
    (d U threshold budget S S' : ℕ)
    (hlower : ∀ o : H.ResidualOption M,
      d ≤ (((H.residualSystem M).fiber
        ((H.residualSystem M).owner o)).card))
    (hjob : ∀ j, ¬ (H.residualSystem M).Covers A j →
      (H.residualSystem M).residualJobDegree ∅ j ≤
        (H.residualSystem M).residualJobDegree A j + U)
    (hupper : ∀ s, (H.residualSystem M).slotDegree s ≤ S)
    (hthreshold : threshold ≤ S' + 1)
    (hbudget : 2 * S ≤ 2 * S' + budget)
    (hshrink : ∀ s : (H.residualSystem M).ActiveSlot threshold,
      (∀ p ∈ A, s.1 ∉ (H.residualSystem M).slots p) →
        2 * (H.residualSystem M).residualSlotDegree A s.1 + budget ≤
          2 * (H.residualSystem M).residualSlotDegree ∅ s.1) :
    (∀ q : H.ResidualOption (M ∪ H.liftResidualSet M A),
      d - U ≤ ((H.residualSystem (M ∪ H.liftResidualSet M A)).fiber
        ((H.residualSystem (M ∪ H.liftResidualSet M A)).owner q)).card) ∧
    (∀ s,
      (H.residualSystem (M ∪ H.liftResidualSet M A)).slotDegree s ≤ S') := by
  let R := H.residualSystem M
  have hjob' := R.residual_owner_fiber_card_ge_sub A d U hlower hjob
  have hslot' := R.residualSlotDegree_le_of_active_shrink
    A threshold budget S S' hupper hthreshold hbudget hshrink
  constructor
  · intro q
    let p := (H.residualUnionEquiv M A).symm q
    have hp := hjob' p
    rw [H.residualSystem_union_fiber_card M A
      ((R.residualSystem A).owner p)] at hp
    have howner :
        (R.residualSystem A).owner p =
          (H.residualSystem
            (M ∪ H.liftResidualSet M A)).owner q := by
      have hpq : (H.residualUnionEquiv M A) p = q := by
        dsimp only [p]
        exact (H.residualUnionEquiv M A).apply_symm_apply q
      exact (H.residualUnionEquiv_owner M A p).symm.trans
        (congrArg
          (H.residualSystem
            (M ∪ H.liftResidualSet M A)).owner hpq)
    rw [howner] at hp
    exact hp
  · intro s
    rw [← H.residualSystem_union_slotDegree M A s]
    change
      (((Finset.univ : Finset (R.ResidualOption A)).filter fun o ↦
        s ∈ (R.residualSystem A).slots o).card ≤ S')
    rw [R.residualSystem_slotDegree_card]
    exact hslot' s

end WeightedEdgeColoring.RankThreeOptionSystem
