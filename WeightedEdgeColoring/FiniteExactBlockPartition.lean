import Mathlib.Data.Finset.SDiff
import Mathlib.Tactic

/-!
# Exact finite block partitions

A finite set can be split into disjoint blocks of a prescribed positive
size and one remainder smaller than a block.  This elementary lemma is the
combinatorial core of finite harmonic packet grouping.
-/

namespace WeightedEdgeColoring

variable {α : Type*} [DecidableEq α]

/-- A partition into full blocks of size `r` and a short remainder. -/
structure ExactBlockPartition (S : Finset α) (r : ℕ) where
  blocks : Finset (Finset α)
  remainder : Finset α
  block_subset : ∀ A ∈ blocks, A ⊆ S
  block_card : ∀ A ∈ blocks, A.card = r
  blocks_disjoint : ∀ A ∈ blocks, ∀ B ∈ blocks, A ≠ B → Disjoint A B
  remainder_subset : remainder ⊆ S
  remainder_disjoint : ∀ A ∈ blocks, Disjoint A remainder
  cover : blocks.biUnion id ∪ remainder = S
  remainder_card_lt : remainder.card < r
  card_decomposition : blocks.card * r + remainder.card = S.card

/-- Every finite set has an exact block partition for each positive block
size. -/
theorem exists_exactBlockPartition (S : Finset α) (r : ℕ) (hr : 0 < r) :
    Nonempty (ExactBlockPartition S r) := by
  classical
  induction S using Finset.strongInductionOn with
  | _ S ih =>
      by_cases hsmall : S.card < r
      · exact ⟨{
          blocks := ∅
          remainder := S
          block_subset := by simp
          block_card := by simp
          blocks_disjoint := by simp
          remainder_subset := Finset.Subset.rfl
          remainder_disjoint := by simp
          cover := by simp
          remainder_card_lt := hsmall
          card_decomposition := by simp }⟩
      · have hrle : r ≤ S.card := Nat.le_of_not_gt hsmall
        obtain ⟨A, hAS, hAcard⟩ := Finset.exists_subset_card_eq hrle
        have hAne : A.Nonempty := Finset.card_pos.mp (hAcard.symm ▸ hr)
        let S' := S \ A
        have hS'ssub : S' ⊂ S := by
          exact Finset.sdiff_ssubset hAS hAne
        obtain ⟨P⟩ := ih S' hS'ssub
        have hAnot : A ∉ P.blocks := by
          intro hAblock
          obtain ⟨x, hxA⟩ := hAne
          have hxS' : x ∈ S' := P.block_subset A hAblock hxA
          exact (Finset.mem_sdiff.mp hxS').2 hxA
        refine ⟨{
          blocks := insert A P.blocks
          remainder := P.remainder
          block_subset := ?_
          block_card := ?_
          blocks_disjoint := ?_
          remainder_subset := ?_
          remainder_disjoint := ?_
          cover := ?_
          remainder_card_lt := P.remainder_card_lt
          card_decomposition := ?_ }⟩
        · intro B hB
          rcases Finset.mem_insert.mp hB with rfl | hB
          · exact hAS
          · exact (P.block_subset B hB).trans Finset.sdiff_subset
        · intro B hB
          rcases Finset.mem_insert.mp hB with rfl | hB
          · exact hAcard
          · exact P.block_card B hB
        · intro B hB C hC hBC
          rcases Finset.mem_insert.mp hB with rfl | hB <;>
            rcases Finset.mem_insert.mp hC with rfl | hC
          · exact (hBC rfl).elim
          · apply Finset.disjoint_left.mpr
            intro x hxA hxC
            have hxS' := P.block_subset C hC hxC
            exact (Finset.mem_sdiff.mp hxS').2 hxA
          · apply Finset.disjoint_left.mpr
            intro x hxB hxA
            have hxS' := P.block_subset B hB hxB
            exact (Finset.mem_sdiff.mp hxS').2 hxA
          · exact P.blocks_disjoint B hB C hC hBC
        · exact P.remainder_subset.trans Finset.sdiff_subset
        · intro B hB
          rcases Finset.mem_insert.mp hB with rfl | hB
          · apply Finset.disjoint_left.mpr
            intro x hxA hxR
            have hxS' := P.remainder_subset hxR
            exact (Finset.mem_sdiff.mp hxS').2 hxA
          · exact P.remainder_disjoint B hB
        · calc
            (insert A P.blocks).biUnion id ∪ P.remainder =
                A ∪ (P.blocks.biUnion id ∪ P.remainder) := by
              simp [Finset.union_assoc]
            _ = A ∪ (S \ A) := by rw [P.cover]
            _ = S := Finset.union_sdiff_of_subset hAS
        · have hblockcard : (insert A P.blocks).card = P.blocks.card + 1 := by
            simp [hAnot]
          have hS'diff : S'.card = S.card - A.card := by
            exact Finset.card_sdiff_of_subset hAS
          rw [hblockcard]
          calc
            (P.blocks.card + 1) * r + P.remainder.card =
                (P.blocks.card * r + P.remainder.card) + r := by
              simp [Nat.add_mul]
              omega
            _ = S'.card + r := by rw [P.card_decomposition]
            _ = S'.card + A.card := by rw [hAcard]
            _ = S.card := Finset.card_sdiff_add_card_eq_card hAS

end WeightedEdgeColoring
