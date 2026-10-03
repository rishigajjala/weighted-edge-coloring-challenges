import WeightedEdgeColoring.RankThreeResidualInclusionExclusion
import WeightedEdgeColoring.RankThreeIsolatedNibble

/-!
# Exact residual collision deficits

The linear deletion load overcounts exactly when one deleted option has more
than one selected blocker.  Rank two and the disjointness of a partial
matching imply that this multiplicity is at most two.
-/

namespace WeightedEdgeColoring

open scoped BigOperators
open FiniteBernoulliChernoff

section Generic

variable {α β : Type*} [Fintype α] [Fintype β]
  [DecidableEq α] [DecidableEq β]

/-- Number of members of `A` whose associated set contains `x`. -/
def blockerMultiplicity (A : Finset α) (F : α → Finset β) (x : β) : ℕ :=
  (A.filter fun a ↦ x ∈ F a).card

/-- Total excess multiplicity beyond the first cover of each point. -/
def collisionDeficit (A : Finset α) (F : α → Finset β) : ℕ :=
  ∑ x ∈ A.biUnion F, (blockerMultiplicity A F x - 1)

/-- Double-counting identity for incidences between indices and covered
points. -/
theorem sum_card_eq_sum_blockerMultiplicity
    (A : Finset α) (F : α → Finset β) :
    (∑ a ∈ A, (F a).card) =
      ∑ x ∈ A.biUnion F, blockerMultiplicity A F x := by
  classical
  calc
    (∑ a ∈ A, (F a).card) =
        ∑ a ∈ A, ∑ x : β, if x ∈ F a then 1 else 0 := by simp
    _ = ∑ x : β, ∑ a ∈ A, if x ∈ F a then 1 else 0 := by
      rw [Finset.sum_comm]
    _ = ∑ x : β, blockerMultiplicity A F x := by
      apply Finset.sum_congr rfl
      intro x _
      simp [blockerMultiplicity]
    _ = ∑ x ∈ A.biUnion F, blockerMultiplicity A F x := by
      symm
      apply Finset.sum_subset (Finset.subset_univ _)
      intro x _ hx
      unfold blockerMultiplicity
      rw [Finset.card_eq_zero]
      ext a
      simp only [Finset.mem_filter]
      constructor
      · intro h
        exfalso
        exact hx (Finset.mem_biUnion.mpr ⟨a, h.1, h.2⟩)
      · intro h
        simp at h

/-- The singleton-cardinality sum equals the union cardinality plus its exact
collision deficit. -/
theorem sum_card_eq_card_biUnion_add_collisionDeficit
    (A : Finset α) (F : α → Finset β) :
    (∑ a ∈ A, (F a).card) =
      (A.biUnion F).card + collisionDeficit A F := by
  rw [sum_card_eq_sum_blockerMultiplicity]
  unfold collisionDeficit
  have hcard : (A.biUnion F).card = ∑ _x ∈ A.biUnion F, 1 := by simp
  rw [hcard]
  calc
    (∑ x ∈ A.biUnion F, blockerMultiplicity A F x) =
        ∑ x ∈ A.biUnion F, (1 + (blockerMultiplicity A F x - 1)) := by
      apply Finset.sum_congr rfl
      intro x hx
      have hpos : 1 ≤ blockerMultiplicity A F x := by
        rcases Finset.mem_biUnion.mp hx with ⟨a, ha, hxa⟩
        unfold blockerMultiplicity
        exact Finset.card_pos.mpr ⟨a, Finset.mem_filter.mpr ⟨ha, hxa⟩⟩
      omega
    _ = (∑ x ∈ A.biUnion F, 1) +
        ∑ x ∈ A.biUnion F, (blockerMultiplicity A F x - 1) := by
      rw [Finset.sum_add_distrib]

/-- The ordered pair-overlap statistic, written as a full-coordinate sum.
This form is convenient for Bernoulli expectations. -/
def pairCollisionStatistic (F : α → Finset β) (S : Finset α) : ℕ :=
  ∑ a : α, ∑ b ∈ (Finset.univ : Finset α).filter (fun b ↦ b ≠ a),
    if a ∈ S ∧ b ∈ S then (F a ∩ F b).card else 0

theorem pairCollisionStatistic_eq_orderedPairOverlap
    (F : α → Finset β) (S : Finset α) :
    pairCollisionStatistic F S = orderedPairOverlap S F := by
  classical
  unfold pairCollisionStatistic orderedPairOverlap
  calc
    (∑ a : α, ∑ b ∈ (Finset.univ : Finset α).filter (fun b ↦ b ≠ a),
        if a ∈ S ∧ b ∈ S then (F a ∩ F b).card else 0) =
        ∑ a : α, if a ∈ S then
          (∑ b ∈ S.filter (fun b ↦ b ≠ a), (F a ∩ F b).card) else 0 := by
      apply Finset.sum_congr rfl
      intro a _
      by_cases ha : a ∈ S
      · simp only [ha, true_and, if_true]
        symm
        calc
          (∑ b ∈ S.filter (fun b ↦ b ≠ a), (F a ∩ F b).card) =
              ∑ b ∈ S.filter (fun b ↦ b ≠ a),
                if b ∈ S then (F a ∩ F b).card else 0 := by
            apply Finset.sum_congr rfl
            intro b hb
            rw [if_pos (Finset.mem_filter.mp hb).1]
          _ = ∑ b ∈ (Finset.univ : Finset α).filter (fun b ↦ b ≠ a),
                if b ∈ S then (F a ∩ F b).card else 0 := by
            apply Finset.sum_subset
            · intro b hb
              have hb' := Finset.mem_filter.mp hb
              exact Finset.mem_filter.mpr ⟨Finset.mem_univ b, hb'.2⟩
            · intro b hb hnot
              have hbS : b ∉ S := by
                intro hbS
                exact hnot (Finset.mem_filter.mpr
                  ⟨hbS, (Finset.mem_filter.mp hb).2⟩)
              simp [hbS]
      · simp [ha]
    _ = ∑ a ∈ S, ∑ b ∈ S.filter (fun b ↦ b ≠ a),
        (F a ∩ F b).card := by
      simp

/-- The ordered collision-pair count dominates twice the exact excess
multiplicity. -/
theorem two_mul_collisionDeficit_le_pairCollisionStatistic
    (A : Finset α) (F : α → Finset β) :
    2 * collisionDeficit A F ≤ pairCollisionStatistic F A := by
  have hexact := sum_card_eq_card_biUnion_add_collisionDeficit A F
  have hbon :=
    two_mul_sum_card_le_two_mul_card_biUnion_add_orderedPairOverlap A F
  rw [pairCollisionStatistic_eq_orderedPairOverlap F A]
  omega

/-- Exact quadratic expectation of the ordered pair-collision statistic under
independent Bernoulli retention. -/
theorem expected_pairCollisionStatistic
    (q : α → ℝ) (F : α → Finset β) :
    (∑ S : Finset α, bernoulliMass q S *
      (pairCollisionStatistic F S : ℝ)) =
      ∑ a : α, ∑ b ∈ (Finset.univ : Finset α).filter (fun b ↦ b ≠ a),
        q a * q b * ((F a ∩ F b).card : ℝ) := by
  classical
  unfold pairCollisionStatistic
  simp_rw [Nat.cast_sum, Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro a _
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro b hb
  have hab : a ≠ b := by
    simpa using (Finset.mem_filter.mp hb).2.symm
  have hpair := FiniteBernoulliThinning.sum_bernoulliMass_indicator_pair q hab
  simp only [Nat.cast_ite, Nat.cast_zero]
  calc
    (∑ S : Finset α, bernoulliMass q S *
        (if a ∈ S ∧ b ∈ S then ((F a ∩ F b).card : ℝ) else 0)) =
        ((F a ∩ F b).card : ℝ) *
          (∑ S : Finset α,
            if a ∈ S ∧ b ∈ S then bernoulliMass q S else 0) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro S _
      by_cases hS : a ∈ S ∧ b ∈ S <;> simp [hS, mul_comm]
    _ = ((F a ∩ F b).card : ℝ) * (q a * q b) := by rw [hpair]
    _ = q a * q b * ((F a ∩ F b).card : ℝ) := by ring

end Generic

namespace RankThreeOptionSystem

universe u v w

variable {Job : Type u} {Slot : Type v} {Option : Type w}
  [Fintype Job] [Fintype Slot] [Fintype Option]
  [DecidableEq Job] [DecidableEq Slot] [DecidableEq Option]
  (H : RankThreeOptionSystem Job Slot Option)

/-- An option of an uncovered job can meet at most two mutually disjoint
selected slot sets. -/
theorem externalBlockerMultiplicity_le_two
    (A : Finset Option) (j : Job) (o : Option)
    (hA : H.IsPartialMatching A) :
    blockerMultiplicity A (H.externalBlockedBy j) o ≤ 2 := by
  let B := A.filter fun p ↦ o ∈ H.externalBlockedBy j p
  let meet : Option → Finset Slot := fun p ↦ H.slots p ∩ H.slots o
  have hdisj : (B : Set Option).PairwiseDisjoint meet := by
    intro p hp r hr hpr
    have hpA : p ∈ A := (Finset.mem_filter.mp hp).1
    have hrA : r ∈ A := (Finset.mem_filter.mp hr).1
    have hslots := hA.1 hpA hrA hpr
    exact hslots.mono Finset.inter_subset_left Finset.inter_subset_left
  have hnonempty : ∀ p ∈ B, (meet p).Nonempty := by
    intro p hp
    have hop := (Finset.mem_filter.mp hp).2
    by_cases hpj : H.owner p = j
    · simp [externalBlockedBy, hpj] at hop
    have hop' : o ∈ H.blockedBy j p := by
      simpa [externalBlockedBy, hpj] using hop
    have hn := (H.mem_blockedBy.mp hop').2
    rw [Compatible, Finset.not_disjoint_iff] at hn
    rcases hn with ⟨s, hso, hsp⟩
    exact ⟨s, Finset.mem_inter.mpr ⟨hsp, hso⟩⟩
  have hunion : B.biUnion meet ⊆ H.slots o := by
    intro s hs
    rcases Finset.mem_biUnion.mp hs with ⟨p, hp, hsm⟩
    exact (Finset.mem_inter.mp hsm).2
  change B.card ≤ 2
  exact (Finset.card_le_card_biUnion hdisj hnonempty).trans
    ((Finset.card_le_card hunion).trans (H.slots_card_le_two o))

/-- Exact first-order update for an uncovered job: linear load is actual
deletion plus the collision deficit. -/
theorem externalJobDeletionLoad_eq_removed_add_collisionDeficit
    (A : Finset Option) (j : Job) (huncovered : ¬ H.Covers A j) :
    H.externalJobDeletionLoad A j =
      (H.removedResidualFiber ∅ A j).card +
        collisionDeficit A (H.externalBlockedBy j) := by
  rw [externalJobDeletionLoad,
    sum_card_eq_card_biUnion_add_collisionDeficit,
    ← H.removedResidualFiber_empty_eq_externalBlockers A j huncovered]

/-- At an unused slot, one option has at most two selected blockers: at most
one with the same owner, and at most one meeting its only possible slot other
than `s`. -/
theorem slotBlockerMultiplicity_le_two
    (A : Finset Option) (s : Slot) (o : Option)
    (hA : H.IsPartialMatching A)
    (hunused : ∀ p ∈ A, s ∉ H.slots p) :
    blockerMultiplicity A (H.slotBlockedBy s) o ≤ 2 := by
  let B := A.filter fun p ↦ o ∈ H.slotBlockedBy s p
  by_cases hB : B.Nonempty
  · obtain ⟨p₀, hp₀B⟩ := hB
    have hp₀data := Finset.mem_filter.mp hp₀B
    have hos : s ∈ H.slots o := by
      have hmem := Finset.mem_filter.mp hp₀data.2
      exact (Finset.mem_filter.mp hmem.1).2
    let BO := B.filter fun p ↦ H.owner o = H.owner p
    let BC := B.filter fun p ↦ ¬ H.Compatible o p
    have hBsub : B ⊆ BO ∪ BC := by
      intro p hp
      have hpdata := Finset.mem_filter.mp hp
      have hbad := (Finset.mem_filter.mp hpdata.2).2
      rcases hbad with howner | hincompat
      · exact Finset.mem_union_left _ (Finset.mem_filter.mpr ⟨hp, howner⟩)
      · exact Finset.mem_union_right _ (Finset.mem_filter.mpr ⟨hp, hincompat⟩)
    have hBO : BO.card ≤ 1 := by
      rw [Finset.card_le_one_iff]
      intro p r hp hr
      have hp' := Finset.mem_filter.mp hp
      have hr' := Finset.mem_filter.mp hr
      have hpA : p ∈ A := (Finset.mem_filter.mp hp'.1).1
      have hrA : r ∈ A := (Finset.mem_filter.mp hr'.1).1
      apply hA.2 hpA hrA
      exact hp'.2.symm.trans hr'.2
    let R : Finset Slot := H.slots o \ {s}
    let meet : Option → Finset Slot := fun p ↦ H.slots p ∩ R
    have hmeetDisj : (BC : Set Option).PairwiseDisjoint meet := by
      intro p hp r hr hpr
      have hpB := (Finset.mem_filter.mp hp).1
      have hrB := (Finset.mem_filter.mp hr).1
      have hpA : p ∈ A := (Finset.mem_filter.mp hpB).1
      have hrA : r ∈ A := (Finset.mem_filter.mp hrB).1
      exact (hA.1 hpA hrA hpr).mono
        Finset.inter_subset_left Finset.inter_subset_left
    have hmeetNonempty : ∀ p ∈ BC, (meet p).Nonempty := by
      intro p hp
      have hpdata := Finset.mem_filter.mp hp
      have hincompat := hpdata.2
      rw [Compatible, Finset.not_disjoint_iff] at hincompat
      rcases hincompat with ⟨t, hto, htp⟩
      have htne : t ≠ s := by
        intro hts
        subst t
        have hpA : p ∈ A :=
          (Finset.mem_filter.mp hpdata.1).1
        exact hunused p hpA htp
      refine ⟨t, Finset.mem_inter.mpr ⟨htp, ?_⟩⟩
      exact Finset.mem_sdiff.mpr ⟨hto, by simpa using htne⟩
    have hmeetSub : BC.biUnion meet ⊆ R := by
      intro t ht
      rcases Finset.mem_biUnion.mp ht with ⟨p, hp, htm⟩
      exact (Finset.mem_inter.mp htm).2
    have hR : R.card ≤ 1 := by
      have hcard := H.slots_card_le_two o
      have heq : R = (H.slots o).erase s := by
        ext t
        simp [R, and_comm]
      rw [heq, Finset.card_erase_of_mem hos]
      omega
    have hBC : BC.card ≤ 1 :=
      (Finset.card_le_card_biUnion hmeetDisj hmeetNonempty).trans
        ((Finset.card_le_card hmeetSub).trans hR)
    change B.card ≤ 2
    calc
      B.card ≤ (BO ∪ BC).card := Finset.card_le_card hBsub
      _ ≤ BO.card + BC.card := Finset.card_union_le _ _
      _ ≤ 2 := by omega
  · have hBeq : B = ∅ := Finset.not_nonempty_iff_eq_empty.mp hB
    change B.card ≤ 2
    simp [hBeq]

/-- Exact first-order update at an unused slot. -/
theorem slotDeletionLoad_eq_removed_add_collisionDeficit
    (A : Finset Option) (s : Slot)
    (hunused : ∀ p ∈ A, s ∉ H.slots p) :
    H.slotDeletionLoad A s =
      (H.removedResidualSlot ∅ A s).card +
        collisionDeficit A (H.slotBlockedBy s) := by
  rw [slotDeletionLoad,
    sum_card_eq_card_biUnion_add_collisionDeficit,
    ← H.removedResidualSlot_empty_eq_slotBlockers A s hunused]

end RankThreeOptionSystem

end WeightedEdgeColoring
