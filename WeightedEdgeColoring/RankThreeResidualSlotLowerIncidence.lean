import WeightedEdgeColoring.RankThreeResidualLowerIncidence

/-!
# Lower incidence bounds for residual slot rows

Fix a slot `s` and a target option `o` using `s`.  Every other option with
the same owner as `o` that avoids `s` belongs to `slotBlockedBy s p`: the
same-owner clause alone witnesses the block.  Thus a lower bound on every
job-fibre size, together with an upper bound on every job--`s` codegree,
gives at least `d - lambda` blockers of each target.  Double counting these
incidences gives the corresponding lower bound for the whole slot row.
-/

namespace WeightedEdgeColoring.RankThreeOptionSystem

open scoped BigOperators
open WeightedEdgeColoring.FiniteBernoulliSupportSplit

universe u v w

variable {Job : Type u} {Slot : Type v} {Option : Type w}
  [Fintype Job] [Fintype Slot] [Fintype Option]
  [DecidableEq Job] [DecidableEq Slot] [DecidableEq Option]
  (H : RankThreeOptionSystem Job Slot Option)

/-- Options with the same owner as `o` that do not use `s`. -/
def ownerFiberAvoidingSlot (s : Slot) (o : Option) : Finset Option :=
  (H.fiber (H.owner o)).filter fun p ↦ s ∉ H.slots p

/-- The avoiding part of an owner fibre is the fibre size minus its
job--slot codegree. -/
theorem ownerFiberAvoidingSlot_card (s : Slot) (o : Option) :
    (H.ownerFiberAvoidingSlot s o).card =
      (H.fiber (H.owner o)).card -
        H.jobSlotCodegree (H.owner o) s := by
  have hpartition := Finset.card_filter_add_card_filter_not
    (s := H.fiber (H.owner o)) (p := fun p ↦ s ∈ H.slots p)
  change H.jobSlotCodegree (H.owner o) s +
      (H.ownerFiberAvoidingSlot s o).card =
        (H.fiber (H.owner o)).card at hpartition
  omega

/-- Every target using `s` has at least `d - lambda` same-owner blockers
that avoid `s`, provided its owner fibre has size at least `d` and its
owner--`s` codegree is at most `lambda`. -/
theorem slotBlockerMultiplicity_avoiding_ge_sub
    (s : Slot) (o : Option) (d lambda : ℕ)
    (hos : s ∈ H.slots o)
    (hjobDegree : d ≤ (H.fiber (H.owner o)).card)
    (hjobSlot : H.jobSlotCodegree (H.owner o) s ≤ lambda) :
    d - lambda ≤
      WeightedEdgeColoring.blockerMultiplicity
        ((Finset.univ : Finset Option).filter fun p ↦ s ∉ H.slots p)
        (H.slotBlockedBy s) o := by
  let P : Finset Option :=
    (Finset.univ : Finset Option).filter fun p ↦ s ∉ H.slots p
  have hsub : H.ownerFiberAvoidingSlot s o ⊆
      P.filter fun p ↦ o ∈ H.slotBlockedBy s p := by
    intro p hp
    have hp' := Finset.mem_filter.mp hp
    have hpowner : H.owner p = H.owner o := H.mem_fiber.mp hp'.1
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_filter.mpr ⟨Finset.mem_univ p, hp'.2⟩, ?_⟩
    simp [slotBlockedBy, hos, hpowner]
  have hcard : d - lambda ≤ (H.ownerFiberAvoidingSlot s o).card := by
    rw [H.ownerFiberAvoidingSlot_card]
    calc
      d - lambda ≤ (H.fiber (H.owner o)).card - lambda :=
        Nat.sub_le_sub_right hjobDegree lambda
      _ ≤ (H.fiber (H.owner o)).card -
          H.jobSlotCodegree (H.owner o) s :=
        Nat.sub_le_sub_left hjobSlot (H.fiber (H.owner o)).card
  calc
    d - lambda ≤ (H.ownerFiberAvoidingSlot s o).card := hcard
    _ ≤ (P.filter fun p ↦ o ∈ H.slotBlockedBy s p).card :=
      Finset.card_le_card hsub
    _ = WeightedEdgeColoring.blockerMultiplicity P (H.slotBlockedBy s) o := rfl

/-- Double counting the incidences between options using `s` and
same-owner options avoiding `s`.  Only the degree lower bound for job fibres
and the codegree upper bound at this one slot are used. -/
theorem sum_slotBlockedBy_avoiding_card_ge_slotDegree_mul_sub_of_owners
    (s : Slot) (d lambda : ℕ)
    (hjobDegree : ∀ o, s ∈ H.slots o → d ≤ (H.fiber (H.owner o)).card)
    (hjobSlot : ∀ j, H.jobSlotCodegree j s ≤ lambda) :
    H.slotDegree s * (d - lambda) ≤
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
  change H.slotDegree s * (d - lambda) ≤
    ∑ p ∈ P, (H.slotBlockedBy s p).card
  calc
    H.slotDegree s * (d - lambda) =
        ∑ _o ∈ H.slotOptionFiber s, (d - lambda) := by
      simp [H.slotOptionFiber_card, Nat.mul_comm]
    _ ≤ ∑ o ∈ H.slotOptionFiber s,
        WeightedEdgeColoring.blockerMultiplicity P (H.slotBlockedBy s) o := by
      apply Finset.sum_le_sum
      intro o ho
      exact H.slotBlockerMultiplicity_avoiding_ge_sub
        s o d lambda (H.mem_slotOptionFiber.mp ho)
          (hjobDegree o (H.mem_slotOptionFiber.mp ho))
          (hjobSlot (H.owner o))
    _ ≤ ∑ o : Option,
        WeightedEdgeColoring.blockerMultiplicity P (H.slotBlockedBy s) o := by
      exact Finset.sum_le_sum_of_subset_of_nonneg
        (Finset.subset_univ _) (fun _ _ _ ↦ Nat.zero_le _)
    _ = ∑ p ∈ P, (H.slotBlockedBy s p).card := hsum.symm

/-- Uniform job-degree bounds imply the owner-local hypothesis above. -/
theorem sum_slotBlockedBy_avoiding_card_ge_slotDegree_mul_sub
    (s : Slot) (d lambda : ℕ)
    (hjobDegree : ∀ j, d ≤ (H.fiber j).card)
    (hjobSlot : ∀ j, H.jobSlotCodegree j s ≤ lambda) :
    H.slotDegree s * (d - lambda) ≤
      ∑ p ∈ (Finset.univ : Finset Option).filter
          (fun p ↦ s ∉ H.slots p),
        (H.slotBlockedBy s p).card := by
  exact H.sum_slotBlockedBy_avoiding_card_ge_slotDegree_mul_sub_of_owners
    s d lambda (fun o _hos ↦ hjobDegree (H.owner o)) hjobSlot

/-- The total normalized slot-deletion coefficient is at least the
double-counting lower bound. -/
theorem sum_residualDeleteWeight_slot_ge_of_owners
    (s : Slot) (d lambda : ℕ) (hlambda : 0 < lambda)
    (hjobDegree : ∀ o, s ∈ H.slots o → d ≤ (H.fiber (H.owner o)).card)
    (hjobSlot : ∀ j, H.jobSlotCodegree j s ≤ lambda) :
    (((H.slotDegree s * (d - lambda) : ℕ) : ℝ) /
        ((3 * lambda : ℕ) : ℝ)) ≤
      ∑ p : Option,
        H.residualDeleteWeight lambda (Sum.inr s) p := by
  let P : Finset Option :=
    (Finset.univ : Finset Option).filter fun p ↦ s ∉ H.slots p
  calc
    (((H.slotDegree s * (d - lambda) : ℕ) : ℝ) /
        ((3 * lambda : ℕ) : ℝ)) ≤
        (∑ p ∈ P, ((H.slotBlockedBy s p).card : ℝ)) /
          ((3 * lambda : ℕ) : ℝ) := by
      apply div_le_div_of_nonneg_right
      · exact_mod_cast H.sum_slotBlockedBy_avoiding_card_ge_slotDegree_mul_sub_of_owners
          s d lambda hjobDegree hjobSlot
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

/-- Uniform job-degree bounds are a convenient special case of the
owner-local slot estimate. -/
theorem sum_residualDeleteWeight_slot_ge
    (s : Slot) (d lambda : ℕ) (hlambda : 0 < lambda)
    (hjobDegree : ∀ j, d ≤ (H.fiber j).card)
    (hjobSlot : ∀ j, H.jobSlotCodegree j s ≤ lambda) :
    (((H.slotDegree s * (d - lambda) : ℕ) : ℝ) /
        ((3 * lambda : ℕ) : ℝ)) ≤
      ∑ p : Option,
        H.residualDeleteWeight lambda (Sum.inr s) p := by
  exact H.sum_residualDeleteWeight_slot_ge_of_owners s d lambda hlambda
    (fun o _hos ↦ hjobDegree (H.owner o)) hjobSlot

/-- Under uniform Bernoulli retention, the normalized slot-row mean inherits
the same lower incidence bound. -/
theorem residualDeleteWeight_slot_mean_ge_of_owners
    (rho : ℝ) (s : Slot) (d lambda : ℕ) (hlambda : 0 < lambda)
    (hrho : 0 ≤ rho)
    (hjobDegree : ∀ o, s ∈ H.slots o → d ≤ (H.fiber (H.owner o)).card)
    (hjobSlot : ∀ j, H.jobSlotCodegree j s ≤ lambda) :
    rho * ((((H.slotDegree s * (d - lambda) : ℕ) : ℝ) /
        ((3 * lambda : ℕ) : ℝ))) ≤
      linearRowMean (fun _ : Option ↦ rho)
        (H.residualDeleteWeight lambda) (Sum.inr s) := by
  rw [linearRowMean_uniform_eq_rho_mul_sum]
  exact mul_le_mul_of_nonneg_left
    (H.sum_residualDeleteWeight_slot_ge_of_owners
      s d lambda hlambda hjobDegree hjobSlot) hrho

/-- Uniform lower job degree implies the owner-local mean estimate. -/
theorem residualDeleteWeight_slot_mean_ge
    (rho : ℝ) (s : Slot) (d lambda : ℕ) (hlambda : 0 < lambda)
    (hrho : 0 ≤ rho)
    (hjobDegree : ∀ j, d ≤ (H.fiber j).card)
    (hjobSlot : ∀ j, H.jobSlotCodegree j s ≤ lambda) :
    rho * ((((H.slotDegree s * (d - lambda) : ℕ) : ℝ) /
        ((3 * lambda : ℕ) : ℝ))) ≤
      linearRowMean (fun _ : Option ↦ rho)
        (H.residualDeleteWeight lambda) (Sum.inr s) := by
  exact H.residualDeleteWeight_slot_mean_ge_of_owners
    rho s d lambda hlambda hrho
      (fun o _hos ↦ hjobDegree (H.owner o)) hjobSlot

end WeightedEdgeColoring.RankThreeOptionSystem
