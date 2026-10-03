import WeightedEdgeColoring.RankThreeLinearResidual
import WeightedEdgeColoring.RankThreePairCounting

/-!
# Pair corrections for residual deletion counts

The linear deletion load counts an option once for every selected blocker.
This file identifies the actually deleted set with the union of those blocker
sets, and records the first Bonferroni correction for that overcount.
-/

namespace WeightedEdgeColoring

open scoped BigOperators

section FiniteUnion

variable {α β : Type*} [DecidableEq α] [DecidableEq β]

/-- The sum of intersections over ordered pairs of distinct indices.  Every
unordered pair occurs twice. -/
def orderedPairOverlap (A : Finset α) (F : α → Finset β) : ℕ :=
  ∑ a ∈ A, ∑ b ∈ A.filter (fun b ↦ b ≠ a), (F a ∩ F b).card

/-- The part of `F a` already covered by the remaining family is bounded by
the sum of its pairwise intersections. -/
theorem card_inter_biUnion_le_sum_inter
    (a : α) (A : Finset α) (F : α → Finset β) :
    (F a ∩ A.biUnion F).card ≤ ∑ b ∈ A, (F a ∩ F b).card := by
  calc
    (F a ∩ A.biUnion F).card ≤
        (A.biUnion fun b ↦ F a ∩ F b).card := by
      apply Finset.card_le_card
      intro x hx
      rcases Finset.mem_inter.mp hx with ⟨hxa, hxU⟩
      rcases Finset.mem_biUnion.mp hxU with ⟨b, hb, hxb⟩
      exact Finset.mem_biUnion.mpr ⟨b, hb, Finset.mem_inter.mpr ⟨hxa, hxb⟩⟩
    _ ≤ ∑ b ∈ A, (F a ∩ F b).card := Finset.card_biUnion_le

/-- First Bonferroni inequality for a finite union, written without division:
twice the singleton sum is at most twice the union size plus the ordered-pair
overlap sum. -/
theorem two_mul_sum_card_le_two_mul_card_biUnion_add_orderedPairOverlap
    (A : Finset α) (F : α → Finset β) :
    2 * (∑ a ∈ A, (F a).card) ≤
      2 * (A.biUnion F).card + orderedPairOverlap A F := by
  classical
  induction A using Finset.induction_on with
  | empty => simp [orderedPairOverlap]
  | @insert a A ha ih =>
      have hinter := card_inter_biUnion_le_sum_inter a A F
      have hcard := Finset.card_union_add_card_inter (F a) (A.biUnion F)
      simp only [Finset.biUnion_insert]
      rw [Finset.sum_insert ha]
      have hoverlap :
          orderedPairOverlap (insert a A) F =
            orderedPairOverlap A F +
              2 * (∑ b ∈ A, (F a ∩ F b).card) := by
        have hhead : (insert a A).filter (fun b ↦ b ≠ a) = A := by
          ext b
          simp only [Finset.mem_filter, Finset.mem_insert]
          constructor
          · rintro ⟨hb | hb, hne⟩
            · exact False.elim (hne hb)
            · exact hb
          · intro hb
            exact ⟨Or.inr hb, fun hba ↦ ha (hba ▸ hb)⟩
        have htail :
            (∑ p ∈ A, ∑ r ∈ (insert a A).filter (fun r ↦ r ≠ p),
              (F p ∩ F r).card) =
            ∑ p ∈ A, ((F p ∩ F a).card +
              ∑ r ∈ A.filter (fun r ↦ r ≠ p), (F p ∩ F r).card) := by
          apply Finset.sum_congr rfl
          intro p hp
          have hap : a ≠ p := by
            intro hap
            exact ha (hap ▸ hp)
          have hfilter :
              (insert a A).filter (fun r ↦ r ≠ p) =
                insert a (A.filter (fun r ↦ r ≠ p)) := by
            ext r
            simp only [Finset.mem_filter, Finset.mem_insert]
            constructor
            · rintro ⟨hr | hr, hne⟩
              · exact Or.inl hr
              · exact Or.inr ⟨hr, hne⟩
            · rintro (hr | ⟨hrA, hne⟩)
              · refine ⟨Or.inl hr, ?_⟩
                intro hrp
                exact hap (hr.symm.trans hrp)
              · exact ⟨Or.inr hrA, hne⟩
          rw [hfilter, Finset.sum_insert (by simp [ha])]
        unfold orderedPairOverlap
        rw [Finset.sum_insert ha, hhead, htail]
        simp_rw [Finset.sum_add_distrib]
        have hsymm :
            (∑ p ∈ A, (F p ∩ F a).card) =
              ∑ p ∈ A, (F a ∩ F p).card := by
          apply Finset.sum_congr rfl
          intro p _
          rw [Finset.inter_comm]
        rw [hsymm]
        omega
      rw [hoverlap]
      omega

end FiniteUnion

namespace RankThreeOptionSystem

universe u v w

variable {Job : Type u} {Slot : Type v} {Option : Type w}
  [Fintype Job] [Fintype Slot] [Fintype Option]
  [DecidableEq Job] [DecidableEq Slot] [DecidableEq Option]
  (H : RankThreeOptionSystem Job Slot Option)

/-- For an uncovered job, the options deleted in the first residual update
are exactly the union of the external blocker sets. -/
theorem removedResidualFiber_empty_eq_externalBlockers
    (A : Finset Option) (j : Job) (huncovered : ¬ H.Covers A j) :
    H.removedResidualFiber ∅ A j =
      A.biUnion (H.externalBlockedBy j) := by
  apply Finset.Subset.antisymm
  · exact H.removedResidualFiber_empty_subset_externalBlockers A j huncovered
  · intro o ho
    rcases Finset.mem_biUnion.mp ho with ⟨p, hpA, hop⟩
    have hpowner : H.owner p ≠ j := by
      intro hpj
      exact huncovered ⟨p, hpA, hpj⟩
    have hop' : o ∈ H.blockedBy j p := by
      simpa [externalBlockedBy, hpowner] using hop
    have hdata := H.mem_blockedBy.mp hop'
    apply Finset.mem_sdiff.mpr
    constructor
    · exact H.mem_residualFiber.mpr ⟨hdata.1, by simp⟩
    · intro hres
      have hall := (H.mem_residualFiber.mp hres).2 p (by simpa using hpA)
      exact hdata.2 hall.2

/-- Two compatible selected options have at most `4*lambda` common external
blockers for one job when their cross slot-pair codegrees are at most
`lambda`. -/
theorem card_externalBlockedBy_inter_le_four_mul
    (j : Job) (p r : Option) (lambda : ℕ)
    (hcompat : H.Compatible p r)
    (hpair : ∀ s ∈ H.slots p, ∀ t ∈ H.slots r, s ≠ t →
      H.slotPairCodegree s t ≤ lambda) :
    (H.externalBlockedBy j p ∩ H.externalBlockedBy j r).card ≤
      4 * lambda := by
  let U : Finset Option := (H.slots p).biUnion fun s ↦
    (H.slots r).biUnion fun t ↦ H.slotPairFiber s t
  have hsubset :
      H.externalBlockedBy j p ∩ H.externalBlockedBy j r ⊆ U := by
    intro o ho
    rcases Finset.mem_inter.mp ho with ⟨hop, hor⟩
    by_cases hpj : H.owner p = j
    · simp [externalBlockedBy, hpj] at hop
    by_cases hrj : H.owner r = j
    · simp [externalBlockedBy, hrj] at hor
    have hop' : o ∈ H.blockedBy j p := by
      simpa [externalBlockedBy, hpj] using hop
    have hor' : o ∈ H.blockedBy j r := by
      simpa [externalBlockedBy, hrj] using hor
    have hnop := (H.mem_blockedBy.mp hop').2
    have hnor := (H.mem_blockedBy.mp hor').2
    rw [Compatible, Finset.not_disjoint_iff] at hnop hnor
    rcases hnop with ⟨s, hos, hsp⟩
    rcases hnor with ⟨t, hot, htr⟩
    apply Finset.mem_biUnion.mpr
    refine ⟨s, hsp, Finset.mem_biUnion.mpr ⟨t, htr, ?_⟩⟩
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ o, hos, hot⟩
  calc
    (H.externalBlockedBy j p ∩ H.externalBlockedBy j r).card ≤ U.card :=
      Finset.card_le_card hsubset
    _ ≤ ∑ s ∈ H.slots p,
        ∑ t ∈ H.slots r, (H.slotPairFiber s t).card := by
      exact Finset.card_biUnion_le.trans
        (Finset.sum_le_sum fun s _ ↦ Finset.card_biUnion_le)
    _ ≤ ∑ _s ∈ H.slots p, ∑ _t ∈ H.slots r, lambda := by
      exact Finset.sum_le_sum fun s hs ↦ Finset.sum_le_sum fun t ht ↦ by
        rw [H.slotPairFiber_card]
        apply hpair s hs t ht
        intro hst
        subst t
        exact (Finset.disjoint_left.mp hcompat) hs ht
    _ = (H.slots p).card * ((H.slots r).card * lambda) := by simp
    _ ≤ 2 * (2 * lambda) := by
      exact Nat.mul_le_mul (H.slots_card_le_two p)
        (Nat.mul_le_mul_right lambda (H.slots_card_le_two r))
    _ = 4 * lambda := by omega

/-- The exact residual deletion count satisfies the first pair-corrected
lower bound.  This is the useful complement to the linear union bound. -/
theorem two_mul_externalJobDeletionLoad_le_removed_add_pairOverlap
    (A : Finset Option) (j : Job) (huncovered : ¬ H.Covers A j) :
    2 * H.externalJobDeletionLoad A j ≤
      2 * (H.removedResidualFiber ∅ A j).card +
        orderedPairOverlap A (H.externalBlockedBy j) := by
  rw [H.removedResidualFiber_empty_eq_externalBlockers A j huncovered]
  exact two_mul_sum_card_le_two_mul_card_biUnion_add_orderedPairOverlap
    A (H.externalBlockedBy j)

/-- If `A` is a partial matching and all slot-pair codegrees are at most
`lambda`, each ordered-pair correction in the preceding theorem is at most
`4*lambda`. -/
theorem externalBlocker_orderedPairOverlap_le
    (A : Finset Option) (j : Job) (lambda : ℕ)
    (hA : H.IsPartialMatching A)
    (hpair : ∀ s t, s ≠ t → H.slotPairCodegree s t ≤ lambda) :
    orderedPairOverlap A (H.externalBlockedBy j) ≤
      A.card * (A.card - 1) * (4 * lambda) := by
  unfold orderedPairOverlap
  calc
    (∑ p ∈ A, ∑ r ∈ A.filter (fun r ↦ r ≠ p),
        (H.externalBlockedBy j p ∩ H.externalBlockedBy j r).card) ≤
        ∑ _p ∈ A, ∑ _r ∈ A.filter (fun r ↦ r ≠ _p), 4 * lambda := by
      apply Finset.sum_le_sum
      intro p hp
      apply Finset.sum_le_sum
      intro r hr
      have hrA : r ∈ A := (Finset.mem_filter.mp hr).1
      have hne : r ≠ p := (Finset.mem_filter.mp hr).2
      apply H.card_externalBlockedBy_inter_le_four_mul j p r lambda
      · exact hA.1 hp hrA hne.symm
      · intro s hs t ht hst
        exact hpair s t hst
    _ = A.card * (A.card - 1) * (4 * lambda) := by
      have hfilter (p : Option) (hp : p ∈ A) :
          (A.filter (fun r ↦ r ≠ p)).card = A.card - 1 := by
        have heq : A.filter (fun r ↦ r ≠ p) = A.erase p := by
          ext r
          simp [and_comm]
        rw [heq, Finset.card_erase_of_mem hp]
      calc
        (∑ p ∈ A, ∑ _r ∈ A.filter (fun r ↦ r ≠ p), 4 * lambda) =
            ∑ p ∈ A,
              (A.filter (fun r ↦ r ≠ p)).card * (4 * lambda) := by simp
        _ = ∑ _p ∈ A, (A.card - 1) * (4 * lambda) := by
          apply Finset.sum_congr rfl
          intro p hp
          rw [hfilter p hp]
        _ = A.card * (A.card - 1) * (4 * lambda) := by simp [Nat.mul_assoc]

/-- Explicit first-order lower bound on the true job deletion count: the
linear blocker load loses at most the sum of the pair corrections. -/
theorem two_mul_externalJobDeletionLoad_le_removed_add_four_mul_pairs
    (A : Finset Option) (j : Job) (lambda : ℕ)
    (huncovered : ¬ H.Covers A j)
    (hA : H.IsPartialMatching A)
    (hpair : ∀ s t, s ≠ t → H.slotPairCodegree s t ≤ lambda) :
    2 * H.externalJobDeletionLoad A j ≤
      2 * (H.removedResidualFiber ∅ A j).card +
        A.card * (A.card - 1) * (4 * lambda) := by
  calc
    2 * H.externalJobDeletionLoad A j ≤
        2 * (H.removedResidualFiber ∅ A j).card +
          orderedPairOverlap A (H.externalBlockedBy j) :=
      H.two_mul_externalJobDeletionLoad_le_removed_add_pairOverlap A j huncovered
    _ ≤ 2 * (H.removedResidualFiber ∅ A j).card +
        A.card * (A.card - 1) * (4 * lambda) := by
      gcongr
      exact H.externalBlocker_orderedPairOverlap_le A j lambda hA hpair

/-- For an unused slot, the options at that slot deleted in the first
residual update are exactly the union of the slot-blocker sets. -/
theorem removedResidualSlot_empty_eq_slotBlockers
    (A : Finset Option) (s : Slot)
    (hunused : ∀ p ∈ A, s ∉ H.slots p) :
    H.removedResidualSlot ∅ A s = A.biUnion (H.slotBlockedBy s) := by
  apply Finset.Subset.antisymm
  · exact H.removedResidualSlot_empty_subset_slotBlockers A s hunused
  · intro o ho
    rcases Finset.mem_biUnion.mp ho with ⟨p, hpA, hop⟩
    have hdata := Finset.mem_filter.mp hop
    have hos : s ∈ H.slots o := (Finset.mem_filter.mp hdata.1).2
    have hbad : H.owner o = H.owner p ∨ ¬ H.Compatible o p := hdata.2
    apply Finset.mem_sdiff.mpr
    constructor
    · apply Finset.mem_filter.mpr
      refine ⟨?_, hos⟩
      rw [H.mem_residualOptions]
      simp
    · intro hres
      have hoResidual := (Finset.mem_filter.mp hres).1
      have hall := (H.mem_residualOptions.mp hoResidual) p (by simpa using hpA)
      rcases hbad with howner | hincompat
      · exact hall.1 howner
      · exact hincompat hall.2

/-- Pair-corrected lower bound for deletion at an unused slot. -/
theorem two_mul_slotDeletionLoad_le_removed_add_pairOverlap
    (A : Finset Option) (s : Slot)
    (hunused : ∀ p ∈ A, s ∉ H.slots p) :
    2 * H.slotDeletionLoad A s ≤
      2 * (H.removedResidualSlot ∅ A s).card +
        orderedPairOverlap A (H.slotBlockedBy s) := by
  rw [H.removedResidualSlot_empty_eq_slotBlockers A s hunused]
  exact two_mul_sum_card_le_two_mul_card_biUnion_add_orderedPairOverlap
    A (H.slotBlockedBy s)

end RankThreeOptionSystem

end WeightedEdgeColoring
