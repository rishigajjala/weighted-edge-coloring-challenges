import WeightedEdgeColoring.RankThreeDirectNibbleLLL

/-!
# Explicit cross-polarity degree and product bounds

These are the numerical inputs for the support-refined Harris local lemma.
Pairs and upper deletion rows only pay for overlapping lower coverage rows.
Lower coverage rows pay for overlapping pairs and upper rows.
-/

namespace WeightedEdgeColoring.RankThreeOptionSystem

open scoped BigOperators

universe u v w x y z

variable {Job : Type u} {Slot : Type v} {Option : Type w}
  {Conflict : Type x} {LowerRow : Type y} {UpperRow : Type z}
  [Fintype Job] [Fintype Slot] [Fintype Option]
  [Fintype Conflict] [Fintype LowerRow] [Fintype UpperRow]
  [DecidableEq Job] [DecidableEq Slot] [DecidableEq Option]
  [DecidableEq Conflict] [DecidableEq LowerRow] [DecidableEq UpperRow]

/-- A conflict pair has at most `2 R` cross-polarity neighbors when each
option occurs in at most `R` lower rows. -/
theorem directNibbleCrossNeighbor_pair_card_le
    (left right : Conflict → Option)
    (lowerWeight : LowerRow → Option → ℝ)
    (upperWeight : UpperRow → Option → ℝ) (R : ℕ)
    (hlower : ∀ o, (linearRowIncidence lowerWeight o).card ≤ R)
    (c : Conflict) :
    (directNibbleMixedNeighbor left right lowerWeight upperWeight
      (Sum.inl c)).card ≤ 2 * R := by
  apply (directNibbleMixedNeighbor_card_le left right lowerWeight upperWeight
    (Sum.inl c) R ?_).trans
  · exact Nat.mul_le_mul_right R (conflictPairSupport_card_le_two left right c)
  · intro o
    rw [mixedIncidence_pair_card left right lowerWeight upperWeight c o]
    exact hlower o

/-- An upper row with support size `K` has at most `K R` cross-polarity
neighbors when each option occurs in at most `R` lower rows. -/
theorem directNibbleCrossNeighbor_upper_card_le
    (left right : Conflict → Option)
    (lowerWeight : LowerRow → Option → ℝ)
    (upperWeight : UpperRow → Option → ℝ) (R : ℕ)
    (hlower : ∀ o, (linearRowIncidence lowerWeight o).card ≤ R)
    (r : UpperRow) :
    (directNibbleMixedNeighbor left right lowerWeight upperWeight
      (Sum.inr (Sum.inr r))).card ≤
        (linearRowSupport upperWeight r).card * R := by
  apply directNibbleMixedNeighbor_card_le left right lowerWeight upperWeight
    (Sum.inr (Sum.inr r)) R
  intro o
  rw [mixedIncidence_upper_card left right lowerWeight upperWeight r o]
  exact hlower o

/-- A lower row pays only for pair conflicts and upper rows. -/
theorem directNibbleCrossNeighbor_lower_card_le
    (left right : Conflict → Option)
    (lowerWeight : LowerRow → Option → ℝ)
    (upperWeight : UpperRow → Option → ℝ) (D U : ℕ)
    (hconflict : ∀ o,
      (optionConflictIncidence left right o).card ≤ D)
    (hupper : ∀ o, (linearRowIncidence upperWeight o).card ≤ U)
    (r : LowerRow) :
    (directNibbleMixedNeighbor left right lowerWeight upperWeight
      (Sum.inr (Sum.inl r))).card ≤
        (linearRowSupport lowerWeight r).card * (D + U) := by
  apply directNibbleMixedNeighbor_card_le left right lowerWeight upperWeight
    (Sum.inr (Sum.inl r)) (D + U)
  intro o
  rw [mixedIncidence_lower_card left right lowerWeight upperWeight r o]
  exact Nat.add_le_add (hconflict o) (hupper o)

/-- Local form of the standard product estimate.  Only weights of actual
neighbors need to lie below `cap`. -/
theorem one_sub_cap_pow_le_neighbor_product_of_mem
    {B : Type*} [Fintype B] [DecidableEq B]
    (neighbor : B → Finset B) (x : B → ℝ) (cap : ℝ) (d : ℕ) (b : B)
    (hcap0 : 0 ≤ cap) (hcap1 : cap ≤ 1)
    (hxcap : ∀ a ∈ neighbor b, x a ≤ cap)
    (hdegree : (neighbor b).card ≤ d) :
    (1 - cap) ^ d ≤ ∏ a ∈ neighbor b, (1 - x a) := by
  calc
    (1 - cap) ^ d ≤ (1 - cap) ^ (neighbor b).card :=
      pow_le_pow_of_le_one (sub_nonneg.mpr hcap1)
        (sub_le_self 1 hcap0) hdegree
    _ = ∏ _a ∈ neighbor b, (1 - cap) := by simp
    _ ≤ ∏ a ∈ neighbor b, (1 - x a) := by
      apply Finset.prod_le_prod
      · intro a ha
        exact sub_nonneg.mpr hcap1
      · intro a ha
        exact sub_le_sub_left (hxcap a ha) 1

/-- Pair events pay only the lower-row LLL weight. -/
theorem pair_cross_product_lower_bound
    (left right : Conflict → Option)
    (lowerWeight : LowerRow → Option → ℝ)
    (upperWeight : UpperRow → Option → ℝ)
    (pairX rowX : ℝ) (R : ℕ)
    (hrow0 : 0 ≤ rowX) (hrow1 : rowX ≤ 1)
    (hlower : ∀ o, (linearRowIncidence lowerWeight o).card ≤ R)
    (c : Conflict) :
    (1 - rowX) ^ (2 * R) ≤
      ∏ b ∈ directNibbleMixedNeighbor left right lowerWeight upperWeight
        (Sum.inl c), (1 - directNibbleLLLWeight pairX rowX b) := by
  apply one_sub_cap_pow_le_neighbor_product_of_mem
    (directNibbleMixedNeighbor left right lowerWeight upperWeight)
    (directNibbleLLLWeight pairX rowX) rowX (2 * R) (Sum.inl c)
    hrow0 hrow1
  · intro b hb
    have hpolarity := (Finset.mem_filter.mp hb).2.1
    rcases b with b | b
    · simp [directNibbleIsIncreasing] at hpolarity
    · rcases b with b | b
      · exact le_rfl
      · simp [directNibbleIsIncreasing] at hpolarity
  · exact directNibbleCrossNeighbor_pair_card_le left right lowerWeight
      upperWeight R hlower c

/-- Upper deletion rows also pay only lower-row weights. -/
theorem upper_cross_product_lower_bound
    (left right : Conflict → Option)
    (lowerWeight : LowerRow → Option → ℝ)
    (upperWeight : UpperRow → Option → ℝ)
    (pairX rowX : ℝ) (R : ℕ)
    (hrow0 : 0 ≤ rowX) (hrow1 : rowX ≤ 1)
    (hlower : ∀ o, (linearRowIncidence lowerWeight o).card ≤ R)
    (r : UpperRow) :
    (1 - rowX) ^ ((linearRowSupport upperWeight r).card * R) ≤
      ∏ b ∈ directNibbleMixedNeighbor left right lowerWeight upperWeight
        (Sum.inr (Sum.inr r)),
          (1 - directNibbleLLLWeight pairX rowX b) := by
  apply one_sub_cap_pow_le_neighbor_product_of_mem
    (directNibbleMixedNeighbor left right lowerWeight upperWeight)
    (directNibbleLLLWeight pairX rowX) rowX
    ((linearRowSupport upperWeight r).card * R) (Sum.inr (Sum.inr r))
    hrow0 hrow1
  · intro b hb
    have hpolarity := (Finset.mem_filter.mp hb).2.1
    rcases b with b | b
    · simp [directNibbleIsIncreasing] at hpolarity
    · rcases b with b | b
      · exact le_rfl
      · simp [directNibbleIsIncreasing] at hpolarity
  · exact directNibbleCrossNeighbor_upper_card_le left right lowerWeight
      upperWeight R hlower r

/-- Lower coverage rows pay for pair and upper-row weights, both bounded by
`cap`. -/
theorem lower_cross_product_lower_bound
    (left right : Conflict → Option)
    (lowerWeight : LowerRow → Option → ℝ)
    (upperWeight : UpperRow → Option → ℝ)
    (pairX rowX cap : ℝ) (D U : ℕ)
    (hcap0 : 0 ≤ cap) (hcap1 : cap ≤ 1)
    (hpairCap : pairX ≤ cap) (hrowCap : rowX ≤ cap)
    (hconflict : ∀ o,
      (optionConflictIncidence left right o).card ≤ D)
    (hupper : ∀ o, (linearRowIncidence upperWeight o).card ≤ U)
    (r : LowerRow) :
    (1 - cap) ^ ((linearRowSupport lowerWeight r).card * (D + U)) ≤
      ∏ b ∈ directNibbleMixedNeighbor left right lowerWeight upperWeight
        (Sum.inr (Sum.inl r)),
          (1 - directNibbleLLLWeight pairX rowX b) := by
  apply one_sub_cap_pow_le_neighbor_product_of_mem
    (directNibbleMixedNeighbor left right lowerWeight upperWeight)
    (directNibbleLLLWeight pairX rowX) cap
    ((linearRowSupport lowerWeight r).card * (D + U))
    (Sum.inr (Sum.inl r)) hcap0 hcap1
  · intro b hb
    rcases b with b | b
    · exact hpairCap
    · rcases b with b | b
      · have hpolarity := (Finset.mem_filter.mp hb).2.1
        simp [directNibbleIsIncreasing] at hpolarity
      · exact hrowCap
  · exact directNibbleCrossNeighbor_lower_card_le left right lowerWeight
      upperWeight D U hconflict hupper r

end WeightedEdgeColoring.RankThreeOptionSystem
