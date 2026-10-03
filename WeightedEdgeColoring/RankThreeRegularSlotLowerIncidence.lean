import WeightedEdgeColoring.RankThreeResidualSlotLowerIncidence

/-!
# The two-endpoint lower incidence in a regular rank-three system

Assume every option uses exactly two slots, every job has degree `J`, and
every slot has degree `S`.  Fix an option `o` using `s`, and write `t` for
its other slot.  A selected option avoiding `s` deletes `o` from the
residual `s`-row if it either has the same owner as `o` or uses `t`.

There are at least `J-lambda` options of the first kind and at least
`S-lambda` of the second kind.  Their intersection has size at most
`lambda`.  Thus `o` has at least `J+S-3*lambda` eligible blockers.  This is
the missing second-endpoint term in the regularized nibble.
-/

namespace WeightedEdgeColoring.RankThreeOptionSystem

open scoped BigOperators
open WeightedEdgeColoring.FiniteBernoulliSupportSplit

universe u v w

variable {Job : Type u} {Slot : Type v} {Option : Type w}
  [Fintype Job] [Fintype Slot] [Fintype Option]
  [DecidableEq Job] [DecidableEq Slot] [DecidableEq Option]
  (H : RankThreeOptionSystem Job Slot Option)

/-- Options using `t` but avoiding `s`. -/
def slotFiberAvoidingSlot (s t : Slot) : Finset Option :=
  (H.slotOptionFiber t).filter fun p ↦ s ∉ H.slots p

/-- The avoiding part of a slot fibre is its degree minus the corresponding
slot-pair codegree. -/
theorem slotFiberAvoidingSlot_card (s t : Slot) :
    (H.slotFiberAvoidingSlot s t).card =
      H.slotDegree t - H.slotPairCodegree s t := by
  have hpartition := Finset.card_filter_add_card_filter_not
    (s := H.slotOptionFiber t) (p := fun p ↦ s ∈ H.slots p)
  have hpartition' :
      H.slotPairCodegree s t + (H.slotFiberAvoidingSlot s t).card =
        H.slotDegree t := by
    simpa [slotFiberAvoidingSlot, slotOptionFiber, slotPairCodegree,
      slotDegree, Finset.filter_filter, and_comm] using hpartition
  omega

/-- In an exactly regular system, a target option using `s` has both its
owner fibre and its other-slot fibre available as blockers.  The three
possible overlaps cost at most `3*lambda` in total. -/
theorem slotBlockerMultiplicity_avoiding_ge_regular
    (s : Slot) (o : Option) (J S lambda : ℕ)
    (hos : s ∈ H.slots o)
    (hslotsTwo : ∀ p, (H.slots p).card = 2)
    (hjobDegree : ∀ j, (H.fiber j).card = J)
    (hslotDegree : ∀ t, H.slotDegree t = S)
    (hjobSlot : ∀ j t, H.jobSlotCodegree j t ≤ lambda)
    (hslotPair : ∀ t u, t ≠ u → H.slotPairCodegree t u ≤ lambda) :
    J + S - 3 * lambda ≤
      WeightedEdgeColoring.blockerMultiplicity
        ((Finset.univ : Finset Option).filter fun p ↦ s ∉ H.slots p)
        (H.slotBlockedBy s) o := by
  obtain ⟨x, t, hxt, hslots⟩ := Finset.card_eq_two.mp (hslotsTwo o)
  have hsxt : s = x ∨ s = t := by
    simpa [hslots] using hos
  rcases hsxt with rfl | rfl
  · have hot : t ∈ H.slots o := by simp [hslots]
    have hst : s ≠ t := hxt
    let A : Finset Option := H.ownerFiberAvoidingSlot s o
    let B : Finset Option := H.slotFiberAvoidingSlot s t
    let P : Finset Option :=
      (Finset.univ : Finset Option).filter fun p ↦ s ∉ H.slots p
    let T : Finset Option := P.filter fun p ↦ o ∈ H.slotBlockedBy s p
    have hAsub : A ⊆ T := by
      intro p hp
      have hp' := Finset.mem_filter.mp hp
      have hpowner : H.owner p = H.owner o := H.mem_fiber.mp hp'.1
      apply Finset.mem_filter.mpr
      refine ⟨Finset.mem_filter.mpr ⟨Finset.mem_univ p, hp'.2⟩, ?_⟩
      simp [slotBlockedBy, hslots, hpowner.symm]
    have hBsub : B ⊆ T := by
      intro p hp
      have hp' := Finset.mem_filter.mp hp
      have hpt : t ∈ H.slots p := H.mem_slotOptionFiber.mp hp'.1
      have hbad : ¬ H.Compatible o p := by
        rw [Compatible, Finset.not_disjoint_iff]
        exact ⟨t, hot, hpt⟩
      apply Finset.mem_filter.mpr
      refine ⟨Finset.mem_filter.mpr ⟨Finset.mem_univ p, hp'.2⟩, ?_⟩
      simp [slotBlockedBy, hslots, hbad]
    have hinterSub : A ∩ B ⊆ H.ownerSlotFiber o t := by
      intro p hp
      have hpA := Finset.mem_filter.mp (Finset.mem_inter.mp hp).1
      have hpB := Finset.mem_filter.mp (Finset.mem_inter.mp hp).2
      have hpowner : H.owner p = H.owner o := H.mem_fiber.mp hpA.1
      have hpt : t ∈ H.slots p := H.mem_slotOptionFiber.mp hpB.1
      simp [ownerSlotFiber, H.mem_fiber, hpowner, hpt]
    have hAcard : J - lambda ≤ A.card := by
      rw [show A.card = (H.fiber (H.owner o)).card -
          H.jobSlotCodegree (H.owner o) s by
        simpa [A] using H.ownerFiberAvoidingSlot_card s o]
      rw [hjobDegree]
      exact Nat.sub_le_sub_left (hjobSlot (H.owner o) s) J
    have hBcard : S - lambda ≤ B.card := by
      rw [show B.card = H.slotDegree t - H.slotPairCodegree s t by
        simpa [B] using H.slotFiberAvoidingSlot_card s t]
      rw [hslotDegree]
      exact Nat.sub_le_sub_left (hslotPair s t hst) S
    have hinterCard : (A ∩ B).card ≤ lambda := by
      calc
        (A ∩ B).card ≤ (H.ownerSlotFiber o t).card :=
          Finset.card_le_card hinterSub
        _ = H.jobSlotCodegree (H.owner o) t := H.ownerSlotFiber_card o t
        _ ≤ lambda := hjobSlot (H.owner o) t
    have hunionSub : A ∪ B ⊆ T := Finset.union_subset hAsub hBsub
    have hunionIdentity := Finset.card_union_add_card_inter A B
    unfold WeightedEdgeColoring.blockerMultiplicity
    change J + S - 3 * lambda ≤ T.card
    have hunionCard : J + S - 3 * lambda ≤ (A ∪ B).card := by
      omega
    exact hunionCard.trans (Finset.card_le_card hunionSub)
  · have hox : x ∈ H.slots o := by simp [hslots]
    have hst : s ≠ x := hxt.symm
    let A : Finset Option := H.ownerFiberAvoidingSlot s o
    let B : Finset Option := H.slotFiberAvoidingSlot s x
    let P : Finset Option :=
      (Finset.univ : Finset Option).filter fun p ↦ s ∉ H.slots p
    let T : Finset Option := P.filter fun p ↦ o ∈ H.slotBlockedBy s p
    have hAsub : A ⊆ T := by
      intro p hp
      have hp' := Finset.mem_filter.mp hp
      have hpowner : H.owner p = H.owner o := H.mem_fiber.mp hp'.1
      apply Finset.mem_filter.mpr
      refine ⟨Finset.mem_filter.mpr ⟨Finset.mem_univ p, hp'.2⟩, ?_⟩
      simp [slotBlockedBy, hslots, hpowner.symm]
    have hBsub : B ⊆ T := by
      intro p hp
      have hp' := Finset.mem_filter.mp hp
      have hpx : x ∈ H.slots p := H.mem_slotOptionFiber.mp hp'.1
      have hbad : ¬ H.Compatible o p := by
        rw [Compatible, Finset.not_disjoint_iff]
        exact ⟨x, hox, hpx⟩
      apply Finset.mem_filter.mpr
      refine ⟨Finset.mem_filter.mpr ⟨Finset.mem_univ p, hp'.2⟩, ?_⟩
      simp [slotBlockedBy, hslots, hbad]
    have hinterSub : A ∩ B ⊆ H.ownerSlotFiber o x := by
      intro p hp
      have hpA := Finset.mem_filter.mp (Finset.mem_inter.mp hp).1
      have hpB := Finset.mem_filter.mp (Finset.mem_inter.mp hp).2
      have hpowner : H.owner p = H.owner o := H.mem_fiber.mp hpA.1
      have hpx : x ∈ H.slots p := H.mem_slotOptionFiber.mp hpB.1
      simp [ownerSlotFiber, H.mem_fiber, hpowner, hpx]
    have hAcard : J - lambda ≤ A.card := by
      rw [show A.card = (H.fiber (H.owner o)).card -
          H.jobSlotCodegree (H.owner o) s by
        simpa [A] using H.ownerFiberAvoidingSlot_card s o]
      rw [hjobDegree]
      exact Nat.sub_le_sub_left (hjobSlot (H.owner o) s) J
    have hBcard : S - lambda ≤ B.card := by
      rw [show B.card = H.slotDegree x - H.slotPairCodegree s x by
        simpa [B] using H.slotFiberAvoidingSlot_card s x]
      rw [hslotDegree]
      exact Nat.sub_le_sub_left (hslotPair s x hst) S
    have hinterCard : (A ∩ B).card ≤ lambda := by
      calc
        (A ∩ B).card ≤ (H.ownerSlotFiber o x).card :=
          Finset.card_le_card hinterSub
        _ = H.jobSlotCodegree (H.owner o) x := H.ownerSlotFiber_card o x
        _ ≤ lambda := hjobSlot (H.owner o) x
    have hunionSub : A ∪ B ⊆ T := Finset.union_subset hAsub hBsub
    have hunionIdentity := Finset.card_union_add_card_inter A B
    unfold WeightedEdgeColoring.blockerMultiplicity
    change J + S - 3 * lambda ≤ T.card
    have hunionCard : J + S - 3 * lambda ≤ (A ∪ B).card := by
      omega
    exact hunionCard.trans (Finset.card_le_card hunionSub)

/-- Double counting the preceding pointwise lower bound over all targets
using one slot. -/
theorem sum_slotBlockedBy_avoiding_card_ge_regular
    (s : Slot) (J S lambda : ℕ)
    (hslotsTwo : ∀ p, (H.slots p).card = 2)
    (hjobDegree : ∀ j, (H.fiber j).card = J)
    (hslotDegree : ∀ t, H.slotDegree t = S)
    (hjobSlot : ∀ j t, H.jobSlotCodegree j t ≤ lambda)
    (hslotPair : ∀ t u, t ≠ u → H.slotPairCodegree t u ≤ lambda) :
    S * (J + S - 3 * lambda) ≤
      ∑ p ∈ (Finset.univ : Finset Option).filter
          (fun p ↦ s ∉ H.slots p),
        (H.slotBlockedBy s p).card := by
  let P : Finset Option :=
    (Finset.univ : Finset Option).filter fun p ↦ s ∉ H.slots p
  have hsum :
      (∑ p ∈ P, (H.slotBlockedBy s p).card) =
        ∑ o : Option,
          WeightedEdgeColoring.blockerMultiplicity P (H.slotBlockedBy s) o := by
    calc
      (∑ p ∈ P, (H.slotBlockedBy s p).card) =
          ∑ p ∈ P, ∑ o : Option,
            if o ∈ H.slotBlockedBy s p then 1 else 0 := by simp
      _ = ∑ o : Option, ∑ p ∈ P,
          if o ∈ H.slotBlockedBy s p then 1 else 0 := by
        rw [Finset.sum_comm]
      _ = ∑ o : Option,
          WeightedEdgeColoring.blockerMultiplicity P (H.slotBlockedBy s) o := by
        apply Finset.sum_congr rfl
        intro o _ho
        simp [WeightedEdgeColoring.blockerMultiplicity]
  change S * (J + S - 3 * lambda) ≤
    ∑ p ∈ P, (H.slotBlockedBy s p).card
  calc
    S * (J + S - 3 * lambda) =
        ∑ _o ∈ H.slotOptionFiber s, (J + S - 3 * lambda) := by
      simp [H.slotOptionFiber_card, hslotDegree, Nat.mul_comm]
    _ ≤ ∑ o ∈ H.slotOptionFiber s,
        WeightedEdgeColoring.blockerMultiplicity P (H.slotBlockedBy s) o := by
      apply Finset.sum_le_sum
      intro o ho
      exact H.slotBlockerMultiplicity_avoiding_ge_regular
        s o J S lambda (H.mem_slotOptionFiber.mp ho) hslotsTwo
        hjobDegree hslotDegree hjobSlot hslotPair
    _ ≤ ∑ o : Option,
        WeightedEdgeColoring.blockerMultiplicity P (H.slotBlockedBy s) o := by
      exact Finset.sum_le_sum_of_subset_of_nonneg
        (Finset.subset_univ _) (fun _ _ _ ↦ Nat.zero_le _)
    _ = ∑ p ∈ P, (H.slotBlockedBy s p).card := hsum.symm

/-- The normalized slot-deletion row inherits the full owner-plus-other-slot
incidence. -/
theorem sum_residualDeleteWeight_slot_ge_regular
    (s : Slot) (J S lambda : ℕ) (hlambda : 0 < lambda)
    (hslotsTwo : ∀ p, (H.slots p).card = 2)
    (hjobDegree : ∀ j, (H.fiber j).card = J)
    (hslotDegree : ∀ t, H.slotDegree t = S)
    (hjobSlot : ∀ j t, H.jobSlotCodegree j t ≤ lambda)
    (hslotPair : ∀ t u, t ≠ u → H.slotPairCodegree t u ≤ lambda) :
    (((S * (J + S - 3 * lambda) : ℕ) : ℝ) /
        ((3 * lambda : ℕ) : ℝ)) ≤
      ∑ p : Option,
        H.residualDeleteWeight lambda (Sum.inr s) p := by
  let P : Finset Option :=
    (Finset.univ : Finset Option).filter fun p ↦ s ∉ H.slots p
  calc
    (((S * (J + S - 3 * lambda) : ℕ) : ℝ) /
        ((3 * lambda : ℕ) : ℝ)) ≤
        (∑ p ∈ P, ((H.slotBlockedBy s p).card : ℝ)) /
          ((3 * lambda : ℕ) : ℝ) := by
      apply div_le_div_of_nonneg_right
      · exact_mod_cast H.sum_slotBlockedBy_avoiding_card_ge_regular
          s J S lambda hslotsTwo hjobDegree hslotDegree hjobSlot hslotPair
      · positivity
    _ = ∑ p ∈ P,
        ((H.slotBlockedBy s p).card : ℝ) /
          ((3 * lambda : ℕ) : ℝ) := by
      rw [Finset.sum_div]
    _ = ∑ p : Option,
        H.residualDeleteWeight lambda (Sum.inr s) p := by
      simp only [P, residualDeleteWeight]
      rw [Finset.sum_filter]
      apply Finset.sum_congr rfl
      intro p _hp
      by_cases hps : s ∈ H.slots p <;> simp [hps]

/-- Uniform Bernoulli proposals give the same sharp lower bound on the row
mean. -/
theorem residualDeleteWeight_slot_mean_ge_regular
    (rho : ℝ) (s : Slot) (J S lambda : ℕ) (hlambda : 0 < lambda)
    (hrho : 0 ≤ rho)
    (hslotsTwo : ∀ p, (H.slots p).card = 2)
    (hjobDegree : ∀ j, (H.fiber j).card = J)
    (hslotDegree : ∀ t, H.slotDegree t = S)
    (hjobSlot : ∀ j t, H.jobSlotCodegree j t ≤ lambda)
    (hslotPair : ∀ t u, t ≠ u → H.slotPairCodegree t u ≤ lambda) :
    rho * ((((S * (J + S - 3 * lambda) : ℕ) : ℝ) /
        ((3 * lambda : ℕ) : ℝ))) ≤
      linearRowMean (fun _ : Option ↦ rho)
        (H.residualDeleteWeight lambda) (Sum.inr s) := by
  rw [linearRowMean_uniform_eq_rho_mul_sum]
  exact mul_le_mul_of_nonneg_left
    (H.sum_residualDeleteWeight_slot_ge_regular
      s J S lambda hlambda hslotsTwo hjobDegree hslotDegree
      hjobSlot hslotPair) hrho

end WeightedEdgeColoring.RankThreeOptionSystem
