import WeightedEdgeColoring.RankThreeSharpCollisionBridge
import WeightedEdgeColoring.RankThreeResidualActiveSlotUniform
import WeightedEdgeColoring.FiniteBernoulliReadKCoverage

/-!
# Local supports for slot-collision events

The quadratic collision event at a slot only reads options which avoid that
slot and block at least one option using it.  This file isolates that finite
support and bounds both its size and its incidence across slots.  These are
the structural inputs needed when collision upper tails are added to the
Harris local-lemma round.
-/

namespace WeightedEdgeColoring.RankThreeOptionSystem

open WeightedEdgeColoring.FiniteBernoulliChernoff
open WeightedEdgeColoring.FiniteBernoulliSupportSplit

universe u v w

variable {Job : Type u} {Slot : Type v} {Option : Type w}
  [Fintype Job] [Fintype Slot] [Fintype Option]
  [DecidableEq Job] [DecidableEq Slot] [DecidableEq Option]
  (H : RankThreeOptionSystem Job Slot Option)

/-- Coordinates which can contribute to the collision statistic of `s`.
Coordinates using `s` were already replaced by the empty blocker set. -/
noncomputable def slotCollisionSupport (s : Slot) : Finset Option :=
  Finset.univ.filter fun p => (H.avoidingSlotBlockedBy s p).Nonempty

@[simp] theorem mem_slotCollisionSupport_iff (s : Slot) (p : Option) :
    p ∈ H.slotCollisionSupport s ↔
      (H.avoidingSlotBlockedBy s p).Nonempty := by
  simp [slotCollisionSupport]

theorem avoidingSlotBlockedBy_subset (s : Slot) (p : Option) :
    H.avoidingSlotBlockedBy s p ⊆ H.slotBlockedBy s p := by
  by_cases hps : s ∈ H.slots p
  · simp [avoidingSlotBlockedBy, hps]
  · simp [avoidingSlotBlockedBy, hps]

/-- Removing coordinates which use `s` cannot increase point
multiplicity. -/
theorem avoidingSlotBlockerMultiplicity_univ_le_job_slot
    (s : Slot) (o : Option) (J S : ℕ)
    (hjobDegree : ∀ j, (H.fiber j).card ≤ J)
    (hslotDegree : ∀ t, H.slotDegree t ≤ S) :
    blockerMultiplicity (Finset.univ : Finset Option)
        (H.avoidingSlotBlockedBy s) o ≤ J + 2 * S := by
  apply le_trans ?_
    (H.slotBlockerMultiplicity_univ_le_job_slot
      s o J S hjobDegree hslotDegree)
  unfold blockerMultiplicity
  apply Finset.card_le_card
  intro p hp
  have hpData := Finset.mem_filter.mp hp
  exact Finset.mem_filter.mpr
    ⟨hpData.1, H.avoidingSlotBlockedBy_subset s p hpData.2⟩

/-- The total size of all avoiding-slot blocker sets has the same sharp
separate-scale upper bound as the unrestricted family. -/
theorem sum_avoidingSlotBlockedBy_card_le_slotDegree_mul_add
    (s : Slot) (J S : ℕ)
    (hjobDegree : ∀ j, (H.fiber j).card ≤ J)
    (hslotDegree : ∀ t, H.slotDegree t ≤ S) :
    (∑ p : Option, (H.avoidingSlotBlockedBy s p).card) ≤
      H.slotDegree s * (J + 2 * S) := by
  calc
    (∑ p : Option, (H.avoidingSlotBlockedBy s p).card) ≤
        ∑ p : Option, (H.slotBlockedBy s p).card := by
      exact Finset.sum_le_sum fun p _ =>
        Finset.card_le_card (H.avoidingSlotBlockedBy_subset s p)
    _ ≤ H.slotDegree s * (J + 2 * S) :=
      H.sum_slotBlockedBy_card_le_slotDegree_mul_add
        s J S hjobDegree hslotDegree

theorem avoidingSlotBlockedBy_eq_empty_of_not_mem_support
    (s : Slot) (p : Option) (hp : p ∉ H.slotCollisionSupport s) :
    H.avoidingSlotBlockedBy s p = ∅ := by
  rw [Finset.eq_empty_iff_forall_notMem]
  intro o ho
  exact hp ((H.mem_slotCollisionSupport_iff s p).2 ⟨o, ho⟩)

/-- Deleting coordinates outside the local support does not change the
quadratic collision statistic. -/
theorem pairCollisionStatistic_inter_slotCollisionSupport
    (A : Finset Option) (s : Slot) :
    pairCollisionStatistic (H.avoidingSlotBlockedBy s)
        (A ∩ H.slotCollisionSupport s) =
      pairCollisionStatistic (H.avoidingSlotBlockedBy s) A := by
  classical
  unfold pairCollisionStatistic
  apply Finset.sum_congr rfl
  intro p _hp
  apply Finset.sum_congr rfl
  intro r _hr
  by_cases hpA : p ∈ A <;> by_cases hrA : r ∈ A <;>
    by_cases hpK : p ∈ H.slotCollisionSupport s <;>
    by_cases hrK : r ∈ H.slotCollisionSupport s
  all_goals simp only [Finset.mem_inter, hpA, hrA, hpK, hrK, and_self,
    false_and, and_false, if_false, if_true]
  all_goals first
    | rw [H.avoidingSlotBlockedBy_eq_empty_of_not_mem_support s p hpK]
      simp
    | rw [H.avoidingSlotBlockedBy_eq_empty_of_not_mem_support s r hrK]
      simp

/-- Reconstructing an outcome from its inside coordinates and an empty
outside part gives its intersection with the support. -/
theorem zeroOutside_inside_eq_inter
    (K S : Finset Option) :
    (splitEquiv K).symm ((splitEquiv K S).1, ∅) = S ∩ K := by
  classical
  ext p
  by_cases hpK : p ∈ K
  · let pi : Inside K := ⟨p, hpK⟩
    calc
      p ∈ (splitEquiv K).symm ((splitEquiv K S).1, ∅) ↔
          pi ∈ (splitEquiv K S).1 := by
            simpa [pi] using
              (mem_splitEquiv_symm_inside K
                (splitEquiv K S).1 ∅ pi)
      _ ↔ p ∈ S := by simpa [pi] using mem_splitEquiv_inside K S pi
      _ ↔ p ∈ S ∩ K := by simp [hpK]
  · let po : Outside K := ⟨p, hpK⟩
    calc
      p ∈ (splitEquiv K).symm ((splitEquiv K S).1, ∅) ↔ po ∈ (∅ :
          Finset (Outside K)) := by
            simpa [po] using
              (mem_splitEquiv_symm_outside K
                (splitEquiv K S).1 ∅ po)
      _ ↔ p ∈ S ∩ K := by simp [hpK]

/-- The local quadratic statistic obtained by setting all coordinates
outside the collision support to zero. -/
noncomputable def slotCollisionLocalStatistic (s : Slot)
    (A : Finset (Inside (H.slotCollisionSupport s))) : ℝ :=
  pairCollisionStatistic (H.avoidingSlotBlockedBy s)
    ((splitEquiv (H.slotCollisionSupport s)).symm (A, ∅))

/-- The local upper-tail event used by the cylinder local lemma. -/
noncomputable def slotCollisionLocalBad (s : Slot) (T : ℝ) :
    Finset (Finset (Inside (H.slotCollisionSupport s))) :=
  upperTail (H.slotCollisionLocalStatistic s) T

/-- The cylinder generated by the local collision event is exactly the
global upper tail of the avoiding-slot statistic. -/
theorem insideCylinder_slotCollisionLocalBad
    (s : Slot) (T : ℝ) :
    insideCylinder (H.slotCollisionSupport s)
        (H.slotCollisionLocalBad s T) =
      upperTail
        (fun A : Finset Option =>
          (pairCollisionStatistic (H.avoidingSlotBlockedBy s) A : ℝ)) T := by
  classical
  ext A
  simp only [mem_insideCylinder, slotCollisionLocalBad, upperTail,
    Finset.mem_filter, Finset.mem_univ, true_and,
    slotCollisionLocalStatistic]
  rw [zeroOutside_inside_eq_inter (H.slotCollisionSupport s) A]
  rw [H.pairCollisionStatistic_inter_slotCollisionSupport A s]

/-- The local and global collision tails have exactly the same Bernoulli
mass.  Coordinates outside the support factor out with total mass one. -/
theorem slotCollisionLocalBad_mass_eq_global
    (q : Option → ℝ) (s : Slot) (T : ℝ) :
    WeightedEdgeColoring.FiniteLocalLemma.eventMass
        (bernoulliMass
          (insideParameter q (H.slotCollisionSupport s)))
        (H.slotCollisionLocalBad s T) =
      WeightedEdgeColoring.FiniteLocalLemma.eventMass (bernoulliMass q)
        (upperTail
          (fun A : Finset Option =>
            (pairCollisionStatistic (H.avoidingSlotBlockedBy s) A : ℝ)) T) := by
  rw [← H.insideCylinder_slotCollisionLocalBad s T]
  exact (WeightedEdgeColoring.FiniteBernoulliReadKCoverage.eventMass_insideCylinder
    q (H.slotCollisionSupport s) (H.slotCollisionLocalBad s T)).symm

/-- Collision upper tails are increasing, both globally and after
restriction to their local support. -/
theorem slotCollisionLocalBad_isIncreasing (s : Slot) (T : ℝ) :
    WeightedEdgeColoring.FiniteBernoulliHarris.IsIncreasing
      (H.slotCollisionLocalBad s T) := by
  intro A hA B hAB
  simp only [slotCollisionLocalBad, upperTail, Finset.mem_filter,
    Finset.mem_univ, true_and, slotCollisionLocalStatistic] at hA ⊢
  apply hA.trans
  exact_mod_cast pairCollisionStatistic_mono
    (H.avoidingSlotBlockedBy s)
      (show (splitEquiv (H.slotCollisionSupport s)).symm (A, ∅) ⊆
          (splitEquiv (H.slotCollisionSupport s)).symm (B, ∅) by
        intro p hp
        by_cases hpK : p ∈ H.slotCollisionSupport s
        · let pi : Inside (H.slotCollisionSupport s) := ⟨p, hpK⟩
          have hpiA : pi ∈ A := by
            simpa [pi] using
              (mem_splitEquiv_symm_inside (H.slotCollisionSupport s)
                A ∅ pi).mp hp
          have hpiB := hAB hpiA
          simpa [pi] using
            (mem_splitEquiv_symm_inside (H.slotCollisionSupport s)
              B ∅ pi).mpr hpiB
        · let po : Outside (H.slotCollisionSupport s) := ⟨p, hpK⟩
          have : po ∈ (∅ : Finset (Outside (H.slotCollisionSupport s))) := by
            simpa [po] using
              (mem_splitEquiv_symm_outside (H.slotCollisionSupport s)
                A ∅ po).mp hp
          simp at this)
/-- The collision support is contained in the already existing normalized
slot-deletion row support. -/
theorem slotCollisionSupport_subset_residualDeleteWeight
    (lambda : ℕ) (hlambda : 0 < lambda) (s : Slot) :
    H.slotCollisionSupport s ⊆
      linearRowSupport (H.residualDeleteWeight lambda) (Sum.inr s) := by
  intro p hp
  have hnonempty := (H.mem_slotCollisionSupport_iff s p).1 hp
  have hps : s ∉ H.slots p := by
    intro hps
    simpa [avoidingSlotBlockedBy, hps] using hnonempty
  have hblocked : (H.slotBlockedBy s p).Nonempty := by
    simpa [H.avoidingSlotBlockedBy_eq_of_not_mem s p hps] using hnonempty
  have hcard : (H.slotBlockedBy s p).card ≠ 0 :=
    Finset.card_ne_zero.mpr hblocked
  apply Finset.mem_filter.mpr
  refine ⟨Finset.mem_univ p, ?_⟩
  rw [residualDeleteWeight, if_neg hps]
  exact div_ne_zero (by exact_mod_cast hcard) (by positivity)

/-- Separate job/slot degree bound for one collision support. -/
theorem slotCollisionSupport_card_le_job_slot
    (lambda J S : ℕ) (hlambda : 0 < lambda)
    (hjobDegree : ∀ j, (H.fiber j).card ≤ J)
    (hslotDegree : ∀ s, H.slotDegree s ≤ S) (s : Slot) :
    (H.slotCollisionSupport s).card ≤ S * (J + 2 * S) := by
  exact (Finset.card_le_card
    (H.slotCollisionSupport_subset_residualDeleteWeight lambda hlambda s)).trans
      (H.activeSlot_support_card_le_job_slot
        lambda J S hjobDegree hslotDegree s)

/-- Slots whose quadratic collision event reads coordinate `p`. -/
noncomputable def slotCollisionIncidence (p : Option) : Finset Slot :=
  Finset.univ.filter fun s => p ∈ H.slotCollisionSupport s

/-- Collision-row incidence injects into the incidence of all normalized
residual-deletion rows. -/
theorem slotCollisionIncidence_card_le_residual
    (lambda : ℕ) (hlambda : 0 < lambda) (p : Option) :
    (H.slotCollisionIncidence p).card ≤
      (linearRowIncidence (H.residualDeleteWeight lambda) p).card := by
  classical
  apply Finset.card_le_card_of_injOn
    (fun s : Slot => (Sum.inr s : ResidualDeleteRow Job Slot))
  · intro s hs
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_univ _, ?_⟩
    have hsupport : p ∈ H.slotCollisionSupport s :=
      (Finset.mem_filter.mp hs).2
    exact H.slotCollisionSupport_subset_residualDeleteWeight
      lambda hlambda s hsupport
  · intro s _hs t _ht hst
    exact Sum.inr.inj hst

/-- A coordinate occurs in at most `8D` collision supports under uniform
job and slot degree bounds. -/
theorem slotCollisionIncidence_card_le_eight_mul
    (lambda D : ℕ) (hlambda : 0 < lambda)
    (hjobDegree : ∀ j, (H.fiber j).card ≤ D)
    (hslotDegree : ∀ s, H.slotDegree s ≤ D) (p : Option) :
    (H.slotCollisionIncidence p).card ≤ 8 * D := by
  exact (H.slotCollisionIncidence_card_le_residual lambda hlambda p).trans
    (H.residualDeleteWeight_incidence_card_le_eight_mul
      lambda D hjobDegree hslotDegree p)

end WeightedEdgeColoring.RankThreeOptionSystem
