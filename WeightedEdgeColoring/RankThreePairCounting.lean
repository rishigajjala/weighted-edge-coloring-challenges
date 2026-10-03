import WeightedEdgeColoring.RankThreeExchange
import WeightedEdgeColoring.QuantizedOptions

namespace WeightedEdgeColoring

universe u v w

namespace RankThreeOptionSystem

variable {Job : Type u} {Slot : Type v} {Option : Type w}
  [Fintype Job] [Fintype Slot] [Fintype Option]
  [DecidableEq Job] [DecidableEq Slot] [DecidableEq Option]
  (H : RankThreeOptionSystem Job Slot Option)

/-!
# Counting rank-three options from slot-pair codegrees

Every option uses at most two slots.  Consequently, an option meeting a slot
set `T` at least twice determines one unordered two-subset of `T`.  This file
makes that observation exact and proves the sharp binomial pair-codegree
bound.  A second count treats options crossing from `T` to its complement.
-/

/-- Options using both of two specified slots. -/
def optionsUsingPair (s t : Slot) : Finset Option :=
  Finset.univ.filter fun o ↦ s ∈ H.slots o ∧ t ∈ H.slots o

@[simp] theorem card_optionsUsingPair (s t : Slot) :
    (H.optionsUsingPair s t).card = H.slotPairCodegree s t := rfl

/-- Options whose slot set contains an unordered pair `U`. -/
def optionsContainingPair (U : Finset Slot) : Finset Option :=
  Finset.univ.filter fun o ↦ U ⊆ H.slots o

/-- Options meeting `T` in at least two slots. -/
def optionsUsingTwoOf (T : Finset Slot) : Finset Option :=
  Finset.univ.filter fun o ↦ 2 ≤ (H.slots o ∩ T).card

/-- Every option using two slots of `T` belongs to the family indexed by
some unordered two-subset of `T`. -/
theorem optionsUsingTwoOf_subset_pairUnion (T : Finset Slot) :
    H.optionsUsingTwoOf T ⊆
      (T.powersetCard 2).biUnion (H.optionsContainingPair) := by
  intro o ho
  have hinter : 2 ≤ (H.slots o ∩ T).card :=
    (Finset.mem_filter.mp ho).2
  obtain ⟨U, hUsub, hUcard⟩ := Finset.exists_subset_card_eq hinter
  have hUT : U ⊆ T := by
    intro s hs
    exact (Finset.mem_inter.mp (hUsub hs)).2
  have hUslots : U ⊆ H.slots o := by
    intro s hs
    exact (Finset.mem_inter.mp (hUsub hs)).1
  apply Finset.mem_biUnion.mpr
  refine ⟨U, ?_, ?_⟩
  · exact Finset.mem_powersetCard.mpr ⟨hUT, hUcard⟩
  · exact Finset.mem_filter.mpr ⟨Finset.mem_univ o, hUslots⟩

/-- A two-subset family has size at most the corresponding slot-pair
codegree bound. -/
theorem card_optionsContainingPair_le
    (T U : Finset Slot) (lambda : ℕ)
    (hU : U ∈ T.powersetCard 2)
    (hpair : ∀ s ∈ T, ∀ t ∈ T, s ≠ t →
      H.slotPairCodegree s t ≤ lambda) :
    (H.optionsContainingPair U).card ≤ lambda := by
  have hUdata := Finset.mem_powersetCard.mp hU
  obtain ⟨s, t, hst, hUeq⟩ := Finset.card_eq_two.mp hUdata.2
  have hsU : s ∈ U := by simp [hUeq]
  have htU : t ∈ U := by simp [hUeq]
  have hsT : s ∈ T := hUdata.1 hsU
  have htT : t ∈ T := hUdata.1 htU
  have hp := hpair s hsT t htT hst
  have heq : H.optionsContainingPair U = H.optionsUsingPair s t := by
    ext o
    simp only [optionsContainingPair, optionsUsingPair,
      Finset.mem_filter, Finset.mem_univ, true_and, hUeq]
    constructor
    · intro hsub
      exact ⟨hsub (by simp), hsub (by simp)⟩
    · rintro ⟨hs, ht⟩ x hx
      rcases Finset.mem_insert.mp hx with rfl | hx
      · exact hs
      · have hxt : x = t := by simpa using hx
        exact hxt.symm ▸ ht
  rw [heq, H.card_optionsUsingPair]
  exact hp

/-- Sharp internal-pair bound.  If every distinct pair of slots in `T` has
codegree at most `lambda`, at most `choose(T.card, 2) * lambda` options meet
`T` in two slots. -/
theorem card_optionsUsingTwoOf_le_choose_mul
    (T : Finset Slot) (lambda : ℕ)
    (hpair : ∀ s ∈ T, ∀ t ∈ T, s ≠ t →
      H.slotPairCodegree s t ≤ lambda) :
    (H.optionsUsingTwoOf T).card ≤ Nat.choose T.card 2 * lambda := by
  calc
    (H.optionsUsingTwoOf T).card ≤
        ((T.powersetCard 2).biUnion H.optionsContainingPair).card :=
      Finset.card_le_card (H.optionsUsingTwoOf_subset_pairUnion T)
    _ ≤ ∑ U ∈ T.powersetCard 2,
        (H.optionsContainingPair U).card := Finset.card_biUnion_le
    _ ≤ ∑ _U ∈ T.powersetCard 2, lambda := by
      exact Finset.sum_le_sum fun U hU ↦
        H.card_optionsContainingPair_le T U lambda hU hpair
    _ = (T.powersetCard 2).card * lambda := by simp
    _ = Nat.choose T.card 2 * lambda := by
      rw [Finset.card_powersetCard]

/-- Subfamily form of the sharp internal-pair bound. -/
theorem card_le_choose_mul_of_subset_optionsUsingTwoOf
    {F : Finset Option} (T : Finset Slot) (lambda : ℕ)
    (hF : F ⊆ H.optionsUsingTwoOf T)
    (hpair : ∀ s ∈ T, ∀ t ∈ T, s ≠ t →
      H.slotPairCodegree s t ≤ lambda) :
    F.card ≤ Nat.choose T.card 2 * lambda := by
  exact le_trans (Finset.card_le_card hF)
    (H.card_optionsUsingTwoOf_le_choose_mul T lambda hpair)

/-- Pigeonhole converse to the sharp internal-pair bound. -/
theorem exists_pair_codegree_gt_of_choose_mul_lt
    (T : Finset Slot) (lambda : ℕ)
    (hmany : Nat.choose T.card 2 * lambda <
      (H.optionsUsingTwoOf T).card) :
    ∃ s ∈ T, ∃ t ∈ T, s ≠ t ∧
      lambda < H.slotPairCodegree s t := by
  by_contra hnone
  push Not at hnone
  have hle := H.card_optionsUsingTwoOf_le_choose_mul T lambda
    (fun s hs t ht hst ↦ hnone s hs t ht hst)
  exact (Nat.not_le_of_gt hmany) hle

/-! ## Boundary pairs -/

/-- Options using at least one slot of `T` and at least one slot outside
`T`.  Since every option has at most two slots, these are exactly the
two-slot options crossing the cut of the slot set. -/
def boundaryOptions (T : Finset Slot) : Finset Option :=
  Finset.univ.filter fun o ↦
    (H.slots o ∩ T).Nonempty ∧ (H.slots o \ T).Nonempty

/-- Every boundary option belongs to a pair family indexed by one slot in
`T` and one slot outside `T`. -/
theorem boundaryOptions_subset_pairUnion (T : Finset Slot) :
    H.boundaryOptions T ⊆
      T.biUnion fun s ↦
        ((Finset.univ : Finset Slot) \ T).biUnion fun t ↦
          H.optionsUsingPair s t := by
  intro o ho
  have hdata := (Finset.mem_filter.mp ho).2
  obtain ⟨s, hsinter⟩ := hdata.1
  obtain ⟨t, htdiff⟩ := hdata.2
  have hs := Finset.mem_inter.mp hsinter
  have ht := Finset.mem_sdiff.mp htdiff
  apply Finset.mem_biUnion.mpr
  refine ⟨s, hs.2, ?_⟩
  apply Finset.mem_biUnion.mpr
  refine ⟨t, Finset.mem_sdiff.mpr ⟨Finset.mem_univ t, ht.2⟩, ?_⟩
  exact Finset.mem_filter.mpr ⟨Finset.mem_univ o, hs.1, ht.1⟩

/-- Cross-boundary pair count.  Under a cross-pair codegree bound,
the number of options crossing a slot cut is at most the number of ordered
inside/outside pairs times `lambda`.  Each unordered crossing pair has a
unique inside-first orientation, so this coefficient is sharp. -/
theorem card_boundaryOptions_le_mul_mul
    (T : Finset Slot) (lambda : ℕ)
    (hpair : ∀ s ∈ T, ∀ t ∉ T,
      H.slotPairCodegree s t ≤ lambda) :
    (H.boundaryOptions T).card ≤
      T.card * ((Finset.univ : Finset Slot) \ T).card * lambda := by
  let outside : Finset Slot := (Finset.univ : Finset Slot) \ T
  have hinner : ∀ s ∈ T,
      (outside.biUnion fun t ↦ H.optionsUsingPair s t).card ≤
        outside.card * lambda := by
    intro s hs
    calc
      (outside.biUnion fun t ↦ H.optionsUsingPair s t).card ≤
          ∑ t ∈ outside, (H.optionsUsingPair s t).card :=
        Finset.card_biUnion_le
      _ ≤ ∑ _t ∈ outside, lambda := by
        apply Finset.sum_le_sum
        intro t ht
        have htout : t ∉ T := (Finset.mem_sdiff.mp ht).2
        exact hpair s hs t htout
      _ = outside.card * lambda := by simp
  calc
    (H.boundaryOptions T).card ≤
        (T.biUnion fun s ↦ outside.biUnion fun t ↦
          H.optionsUsingPair s t).card := by
      apply Finset.card_le_card
      simpa [outside] using H.boundaryOptions_subset_pairUnion T
    _ ≤ ∑ s ∈ T,
        (outside.biUnion fun t ↦ H.optionsUsingPair s t).card :=
      Finset.card_biUnion_le
    _ ≤ ∑ _s ∈ T, outside.card * lambda := by
      exact Finset.sum_le_sum hinner
    _ = T.card * outside.card * lambda := by
      simp [Nat.mul_assoc]
    _ = T.card * ((Finset.univ : Finset Slot) \ T).card * lambda := rfl

/-- Subfamily form of the boundary-incidence bound. -/
theorem card_le_mul_mul_of_subset_boundaryOptions
    {F : Finset Option} (T : Finset Slot) (lambda : ℕ)
    (hF : F ⊆ H.boundaryOptions T)
    (hpair : ∀ s ∈ T, ∀ t ∉ T,
      H.slotPairCodegree s t ≤ lambda) :
    F.card ≤ T.card * ((Finset.univ : Finset Slot) \ T).card * lambda := by
  exact le_trans (Finset.card_le_card hF)
    (H.card_boundaryOptions_le_mul_mul T lambda hpair)

/-- Pigeonhole converse for boundary incidence. -/
theorem exists_boundary_pair_codegree_gt
    (T : Finset Slot) (lambda : ℕ)
    (hmany : T.card * ((Finset.univ : Finset Slot) \ T).card * lambda <
      (H.boundaryOptions T).card) :
    ∃ s ∈ T, ∃ t ∉ T, lambda < H.slotPairCodegree s t := by
  by_contra hnone
  push Not at hnone
  have hle := H.card_boundaryOptions_le_mul_mul T lambda
    (fun s hs t ht ↦ hnone s hs t ht)
  exact (Nat.not_le_of_gt hmany) hle

end RankThreeOptionSystem

end WeightedEdgeColoring
