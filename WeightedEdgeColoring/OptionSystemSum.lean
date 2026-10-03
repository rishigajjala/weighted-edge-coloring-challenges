import WeightedEdgeColoring.QuantizedOptions

open scoped BigOperators

namespace WeightedEdgeColoring

/-!
# Disjoint sums of rank-three option systems

Large-edge rounding uses two kinds of choices for the same job: ordinary
color-slot choices and extra-slot choices that leave the edge uncoloured.
This file proves the bookkeeping for adjoining two finite option families.
-/

noncomputable section

universe u v w₁ w₂

namespace RankThreeOptionSystem

variable {Job : Type u} {Slot : Type v}
  {Option₁ : Type w₁} {Option₂ : Type w₂}
  [Fintype Job] [Fintype Slot]
  [Fintype Option₁] [Fintype Option₂]
  [DecidableEq Job] [DecidableEq Slot]
  [DecidableEq Option₁] [DecidableEq Option₂]

/-- The disjoint union of two option families with the same jobs and slots. -/
def sum (H : RankThreeOptionSystem Job Slot Option₁)
    (K : RankThreeOptionSystem Job Slot Option₂) :
    RankThreeOptionSystem Job Slot (Option₁ ⊕ Option₂) where
  owner
    | Sum.inl o => H.owner o
    | Sum.inr p => K.owner p
  slots
    | Sum.inl o => H.slots o
    | Sum.inr p => K.slots p
  slots_card_le_two
    | Sum.inl o => H.slots_card_le_two o
    | Sum.inr p => K.slots_card_le_two p

/-- Put the two fractional mass functions on their corresponding summands. -/
def sumMass (x : Option₁ → ℝ) (y : Option₂ → ℝ) :
    Option₁ ⊕ Option₂ → ℝ
  | Sum.inl o => x o
  | Sum.inr p => y p

@[simp] theorem sum_owner_inl
    (H : RankThreeOptionSystem Job Slot Option₁)
    (K : RankThreeOptionSystem Job Slot Option₂) (o : Option₁) :
    (H.sum K).owner (Sum.inl o) = H.owner o := rfl

@[simp] theorem sum_owner_inr
    (H : RankThreeOptionSystem Job Slot Option₁)
    (K : RankThreeOptionSystem Job Slot Option₂) (p : Option₂) :
    (H.sum K).owner (Sum.inr p) = K.owner p := rfl

@[simp] theorem sum_slots_inl
    (H : RankThreeOptionSystem Job Slot Option₁)
    (K : RankThreeOptionSystem Job Slot Option₂) (o : Option₁) :
    (H.sum K).slots (Sum.inl o) = H.slots o := rfl

@[simp] theorem sum_slots_inr
    (H : RankThreeOptionSystem Job Slot Option₁)
    (K : RankThreeOptionSystem Job Slot Option₂) (p : Option₂) :
    (H.sum K).slots (Sum.inr p) = K.slots p := rfl

@[simp] theorem sumMass_inl (x : Option₁ → ℝ) (y : Option₂ → ℝ)
    (o : Option₁) : sumMass x y (Sum.inl o) = x o := rfl

@[simp] theorem sumMass_inr (x : Option₁ → ℝ) (y : Option₂ → ℝ)
    (p : Option₂) : sumMass x y (Sum.inr p) = y p := rfl

theorem sumMass_nonneg (x : Option₁ → ℝ) (y : Option₂ → ℝ)
    (hx : ∀ o, 0 ≤ x o) (hy : ∀ p, 0 ≤ y p) :
    ∀ z, 0 ≤ sumMass x y z := by
  intro z
  cases z with
  | inl o => exact hx o
  | inr p => exact hy p

/-- Job masses add under disjoint union. -/
theorem sum_sumMass_fiber
    (H : RankThreeOptionSystem Job Slot Option₁)
    (K : RankThreeOptionSystem Job Slot Option₂)
    (x : Option₁ → ℝ) (y : Option₂ → ℝ) (j : Job) :
    (∑ z ∈ (H.sum K).fiber j, sumMass x y z) =
      (∑ o ∈ H.fiber j, x o) + (∑ p ∈ K.fiber j, y p) := by
  classical
  simp [RankThreeOptionSystem.fiber, sum, sumMass, Finset.sum_filter]

/-- Fractional slot loads add under disjoint union. -/
theorem sum_sumMass_using_slot
    (H : RankThreeOptionSystem Job Slot Option₁)
    (K : RankThreeOptionSystem Job Slot Option₂)
    (x : Option₁ → ℝ) (y : Option₂ → ℝ) (s : Slot) :
    (∑ z, if s ∈ (H.sum K).slots z then sumMass x y z else 0) =
      (∑ o, if s ∈ H.slots o then x o else 0) +
        ∑ p, if s ∈ K.slots p then y p else 0 := by
  classical
  simp [sum, sumMass]

/-- Fractional slot-pair loads add under disjoint union. -/
theorem sum_sumMass_using_slotPair
    (H : RankThreeOptionSystem Job Slot Option₁)
    (K : RankThreeOptionSystem Job Slot Option₂)
    (x : Option₁ → ℝ) (y : Option₂ → ℝ) (s t : Slot) :
    (∑ z, if s ∈ (H.sum K).slots z ∧ t ∈ (H.sum K).slots z then
        sumMass x y z else 0) =
      (∑ o, if s ∈ H.slots o ∧ t ∈ H.slots o then x o else 0) +
        ∑ p, if s ∈ K.slots p ∧ t ∈ K.slots p then y p else 0 := by
  classical
  simp [sum, sumMass]

/-- Quantized job degrees split exactly between the two option families. -/
theorem sum_quantizedJobDegree
    (H : RankThreeOptionSystem Job Slot Option₁)
    (K : RankThreeOptionSystem Job Slot Option₂)
    (N : ℕ) (x : Option₁ → ℝ) (y : Option₂ → ℝ) (j : Job) :
    (H.sum K).quantizedJobDegree N (sumMass x y) j =
      H.quantizedJobDegree N x j + K.quantizedJobDegree N y j := by
  classical
  unfold quantizedJobDegree
  simp [sum, sumMass]

/-- Quantized slot degrees split exactly between the two option families. -/
theorem sum_quantized_slotDegree
    (H : RankThreeOptionSystem Job Slot Option₁)
    (K : RankThreeOptionSystem Job Slot Option₂)
    (N : ℕ) (x : Option₁ → ℝ) (y : Option₂ → ℝ) (s : Slot) :
    ((H.sum K).quantized N (sumMass x y)).slotDegree s =
      (H.quantized N x).slotDegree s +
        (K.quantized N y).slotDegree s := by
  classical
  rw [(H.sum K).quantized_slotDegree,
    H.quantized_slotDegree, K.quantized_slotDegree]
  simp [sum, sumMass]

/-- Quantized slot-pair codegrees split exactly between the two families. -/
theorem sum_quantized_slotPairCodegree
    (H : RankThreeOptionSystem Job Slot Option₁)
    (K : RankThreeOptionSystem Job Slot Option₂)
    (N : ℕ) (x : Option₁ → ℝ) (y : Option₂ → ℝ) (s t : Slot) :
    ((H.sum K).quantized N (sumMass x y)).slotPairCodegree s t =
      (H.quantized N x).slotPairCodegree s t +
        (K.quantized N y).slotPairCodegree s t := by
  classical
  rw [(H.sum K).quantized_slotPairCodegree,
    H.quantized_slotPairCodegree, K.quantized_slotPairCodegree]
  simp [sum, sumMass]

end RankThreeOptionSystem

end

end WeightedEdgeColoring
