import WeightedEdgeColoring.OptionSystemSum

open scoped BigOperators

namespace WeightedEdgeColoring

/-!
# Combining option systems on disjoint slot types

Ordinary color slots and leave-uncoloured counting slots must never block
one another.  We therefore embed their slot types into a disjoint sum before
joining their option families.  The lemmas below show that all loads and
codegrees stay entirely on their own side.
-/

noncomputable section

universe u v₁ v₂ w₁ w₂

namespace RankThreeOptionSystem

variable {Job : Type u} {Slot₁ : Type v₁} {Slot₂ : Type v₂}
  {Option₁ : Type w₁} {Option₂ : Type w₂}
  [Fintype Job] [Fintype Slot₁] [Fintype Slot₂]
  [Fintype Option₁] [Fintype Option₂]
  [DecidableEq Job] [DecidableEq Slot₁] [DecidableEq Slot₂]
  [DecidableEq Option₁] [DecidableEq Option₂]

def sumInlEmbedding : Slot₁ ↪ Slot₁ ⊕ Slot₂ where
  toFun := Sum.inl
  inj' := Sum.inl_injective

def sumInrEmbedding : Slot₂ ↪ Slot₁ ⊕ Slot₂ where
  toFun := Sum.inr
  inj' := Sum.inr_injective

/-- Embed all slots of an option system into the left summand. -/
def liftSlotsLeft (H : RankThreeOptionSystem Job Slot₁ Option₁) :
    RankThreeOptionSystem Job (Slot₁ ⊕ Slot₂) Option₁ where
  owner := H.owner
  slots o := (H.slots o).map sumInlEmbedding
  slots_card_le_two o := by
    simpa [Finset.card_map] using H.slots_card_le_two o

/-- Embed all slots of an option system into the right summand. -/
def liftSlotsRight (K : RankThreeOptionSystem Job Slot₂ Option₂) :
    RankThreeOptionSystem Job (Slot₁ ⊕ Slot₂) Option₂ where
  owner := K.owner
  slots p := (K.slots p).map sumInrEmbedding
  slots_card_le_two p := by
    simpa [Finset.card_map] using K.slots_card_le_two p

/-- Join two option systems after placing their slot sets in disjoint
summands. -/
def separatedSum (H : RankThreeOptionSystem Job Slot₁ Option₁)
    (K : RankThreeOptionSystem Job Slot₂ Option₂) :
    RankThreeOptionSystem Job (Slot₁ ⊕ Slot₂) (Option₁ ⊕ Option₂) :=
  (liftSlotsLeft (Slot₂ := Slot₂) H).sum
    (liftSlotsRight (Slot₁ := Slot₁) K)

@[simp] theorem mem_liftSlotsLeft_inl
    (H : RankThreeOptionSystem Job Slot₁ Option₁) (o : Option₁) (s : Slot₁) :
    Sum.inl s ∈ (liftSlotsLeft (Slot₂ := Slot₂) H).slots o ↔
      s ∈ H.slots o := by
  simp [liftSlotsLeft, sumInlEmbedding]

@[simp] theorem not_mem_liftSlotsLeft_inr
    (H : RankThreeOptionSystem Job Slot₁ Option₁) (o : Option₁) (t : Slot₂) :
    Sum.inr t ∉ (liftSlotsLeft (Slot₂ := Slot₂) H).slots o := by
  simp [liftSlotsLeft, sumInlEmbedding]

@[simp] theorem mem_liftSlotsRight_inr
    (K : RankThreeOptionSystem Job Slot₂ Option₂) (p : Option₂) (t : Slot₂) :
    Sum.inr t ∈ (liftSlotsRight (Slot₁ := Slot₁) K).slots p ↔
      t ∈ K.slots p := by
  simp [liftSlotsRight, sumInrEmbedding]

@[simp] theorem not_mem_liftSlotsRight_inl
    (K : RankThreeOptionSystem Job Slot₂ Option₂) (p : Option₂) (s : Slot₁) :
    Sum.inl s ∉ (liftSlotsRight (Slot₁ := Slot₁) K).slots p := by
  simp [liftSlotsRight, sumInrEmbedding]

/-- A real slot sees exactly the original real-option fractional load. -/
theorem separatedSum_sumMass_using_inl
    (H : RankThreeOptionSystem Job Slot₁ Option₁)
    (K : RankThreeOptionSystem Job Slot₂ Option₂)
    (x : Option₁ → ℝ) (y : Option₂ → ℝ) (s : Slot₁) :
    (∑ z, if Sum.inl s ∈ (H.separatedSum K).slots z then
        sumMass x y z else 0) =
      ∑ o, if s ∈ H.slots o then x o else 0 := by
  classical
  simp [separatedSum, sum, sumMass, liftSlotsLeft, liftSlotsRight,
    sumInlEmbedding, sumInrEmbedding]

/-- An extra slot sees exactly the original extra-option fractional load. -/
theorem separatedSum_sumMass_using_inr
    (H : RankThreeOptionSystem Job Slot₁ Option₁)
    (K : RankThreeOptionSystem Job Slot₂ Option₂)
    (x : Option₁ → ℝ) (y : Option₂ → ℝ) (t : Slot₂) :
    (∑ z, if Sum.inr t ∈ (H.separatedSum K).slots z then
        sumMass x y z else 0) =
      ∑ p, if t ∈ K.slots p then y p else 0 := by
  classical
  simp [separatedSum, sum, sumMass, liftSlotsLeft, liftSlotsRight,
    sumInlEmbedding, sumInrEmbedding]

/-- No option can simultaneously use one real slot and one extra slot. -/
theorem separatedSum_cross_slotPairCodegree_eq_zero
    (H : RankThreeOptionSystem Job Slot₁ Option₁)
    (K : RankThreeOptionSystem Job Slot₂ Option₂)
    (s : Slot₁) (t : Slot₂) :
    (H.separatedSum K).slotPairCodegree (Sum.inl s) (Sum.inr t) = 0 := by
  classical
  unfold slotPairCodegree
  simp [separatedSum, sum, liftSlotsLeft, liftSlotsRight,
    sumInlEmbedding, sumInrEmbedding]

/-- Quantized real-slot degree is unchanged by adjoining the separated
extra-option family. -/
theorem separatedSum_quantized_slotDegree_inl
    (H : RankThreeOptionSystem Job Slot₁ Option₁)
    (K : RankThreeOptionSystem Job Slot₂ Option₂)
    (N : ℕ) (x : Option₁ → ℝ) (y : Option₂ → ℝ) (s : Slot₁) :
    ((H.separatedSum K).quantized N (sumMass x y)).slotDegree (Sum.inl s) =
      (H.quantized N x).slotDegree s := by
  classical
  rw [(H.separatedSum K).quantized_slotDegree,
    H.quantized_slotDegree]
  simp [separatedSum, sum, sumMass, liftSlotsLeft, liftSlotsRight,
    sumInlEmbedding, sumInrEmbedding]

/-- Quantized extra-slot degree is unchanged by adjoining the separated
real-option family. -/
theorem separatedSum_quantized_slotDegree_inr
    (H : RankThreeOptionSystem Job Slot₁ Option₁)
    (K : RankThreeOptionSystem Job Slot₂ Option₂)
    (N : ℕ) (x : Option₁ → ℝ) (y : Option₂ → ℝ) (t : Slot₂) :
    ((H.separatedSum K).quantized N (sumMass x y)).slotDegree (Sum.inr t) =
      (K.quantized N y).slotDegree t := by
  classical
  rw [(H.separatedSum K).quantized_slotDegree,
    K.quantized_slotDegree]
  simp [separatedSum, sum, sumMass, liftSlotsLeft, liftSlotsRight,
    sumInlEmbedding, sumInrEmbedding]

/-- Quantized job--slot codegree on a real slot is unchanged by adjoining
the separated extra family. -/
theorem separatedSum_quantized_jobSlotCodegree_inl
    (H : RankThreeOptionSystem Job Slot₁ Option₁)
    (K : RankThreeOptionSystem Job Slot₂ Option₂)
    (N : ℕ) (x : Option₁ → ℝ) (y : Option₂ → ℝ)
    (j : Job) (s : Slot₁) :
    ((H.separatedSum K).quantized N (sumMass x y)).jobSlotCodegree
        j (Sum.inl s) =
      (H.quantized N x).jobSlotCodegree j s := by
  classical
  rw [(H.separatedSum K).quantized_jobSlotCodegree,
    H.quantized_jobSlotCodegree]
  unfold quantizedJobSlotCodegree
  simp [separatedSum, sum, liftSlotsLeft, liftSlotsRight,
    sumInlEmbedding, sumInrEmbedding]

/-- Quantized job--slot codegree on an extra slot is unchanged by adjoining
the separated ordinary family. -/
theorem separatedSum_quantized_jobSlotCodegree_inr
    (H : RankThreeOptionSystem Job Slot₁ Option₁)
    (K : RankThreeOptionSystem Job Slot₂ Option₂)
    (N : ℕ) (x : Option₁ → ℝ) (y : Option₂ → ℝ)
    (j : Job) (t : Slot₂) :
    ((H.separatedSum K).quantized N (sumMass x y)).jobSlotCodegree
        j (Sum.inr t) =
      (K.quantized N y).jobSlotCodegree j t := by
  classical
  rw [(H.separatedSum K).quantized_jobSlotCodegree,
    K.quantized_jobSlotCodegree]
  unfold quantizedJobSlotCodegree
  simp [separatedSum, sum, liftSlotsLeft, liftSlotsRight,
    sumInlEmbedding, sumInrEmbedding]

end RankThreeOptionSystem

end

end WeightedEdgeColoring
