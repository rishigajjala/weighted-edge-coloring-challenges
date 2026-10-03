import Mathlib.Order.Partition.Finpartition
import Mathlib.Tactic

open Finset

namespace WeightedEdgeColoring

/-! # Grouping a finite set into medium-sized blocks -/

/-- If `K` is positive and at most the size of `S`, then `S` can be
partitioned into blocks whose sizes lie between `K` and `2 * K - 1`. -/
theorem exists_finpartition_card_between {α : Type*} [DecidableEq α]
    (S : Finset α) (K : ℕ) (hK : 0 < K) (hKS : K ≤ S.card) :
    ∃ P : Finpartition S,
      ∀ T ∈ P.parts, K ≤ T.card ∧ T.card ≤ 2 * K - 1 := by
  classical
  have aux : ∀ n : ℕ, ∀ S : Finset α, S.card = n → K ≤ S.card →
      ∃ P : Finpartition S,
        ∀ T ∈ P.parts, K ≤ T.card ∧ T.card ≤ 2 * K - 1 := by
    intro n
    induction n using Nat.strong_induction_on with
    | h n ih =>
        intro S hcard hKS
        by_cases hsmall : S.card < 2 * K
        · have hSne : S ≠ ∅ := by
            intro hS
            subst S
            simp at hKS
            omega
          refine ⟨Finpartition.indiscrete hSne, ?_⟩
          intro T hT
          have hTS : T = S := by
            simpa [Finpartition.indiscrete] using hT
          subst T
          omega
        · obtain ⟨T, hTS, hTcard⟩ := Finset.exists_subset_card_eq hKS
          let R := S \ T
          have hRcard : R.card = S.card - K := by
            simp only [R, Finset.card_sdiff_of_subset hTS, hTcard]
          have hKR : K ≤ R.card := by omega
          have hRlt : R.card < n := by omega
          obtain ⟨P, hP⟩ := ih R.card hRlt R rfl hKR
          have hTne : T ≠ ∅ := by
            intro hT
            subst T
            simp at hTcard
            omega
          have hdisj : Disjoint R T := by
            exact Finset.sdiff_disjoint
          have hunion : R ∪ T = S := by
            exact Finset.sdiff_union_of_subset hTS
          let Q : Finpartition S := P.extend hTne hdisj hunion
          refine ⟨Q, ?_⟩
          intro U hU
          change U ∈ insert T P.parts at hU
          rcases Finset.mem_insert.mp hU with hUT | hUP
          · subst U
            omega
          · exact hP U hUP
  exact aux S.card S rfl hKS

/-- The weaker `2 * K` upper bound, often convenient in applications. -/
theorem exists_finpartition_card_between_two_mul {α : Type*} [DecidableEq α]
    (S : Finset α) (K : ℕ) (hK : 0 < K) (hKS : K ≤ S.card) :
    ∃ P : Finpartition S,
      ∀ T ∈ P.parts, K ≤ T.card ∧ T.card ≤ 2 * K := by
  obtain ⟨P, hP⟩ := exists_finpartition_card_between S K hK hKS
  refine ⟨P, fun T hT ↦ ⟨(hP T hT).1, ?_⟩⟩
  exact (hP T hT).2.trans (Nat.sub_le _ _)

/-- Every element of the ground set belongs to exactly one part of the
bounded block partition. -/
theorem exists_finpartition_card_between_existsUnique {α : Type*}
    [DecidableEq α] (S : Finset α) (K : ℕ) (hK : 0 < K)
    (hKS : K ≤ S.card) :
    ∃ P : Finpartition S,
      (∀ T ∈ P.parts, K ≤ T.card ∧ T.card ≤ 2 * K - 1) ∧
      ∀ a ∈ S, ∃! T, T ∈ P.parts ∧ a ∈ T := by
  obtain ⟨P, hP⟩ := exists_finpartition_card_between S K hK hKS
  exact ⟨P, hP, fun a ha ↦ P.existsUnique_mem ha⟩

end WeightedEdgeColoring
