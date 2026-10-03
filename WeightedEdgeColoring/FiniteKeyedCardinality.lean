import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Tactic

/-!
# Cardinality bookkeeping over finite keys

Linear grouping is carried out independently in every endpoint-pair/class
cell.  These lemmas sum a cellwise cardinality estimate without losing a
factor equal to the number of cells.
-/

open scoped BigOperators

namespace WeightedEdgeColoring

universe u v

/-- A finite set is the disjoint union of the fibers of any map to a finite
key type. -/
theorem card_eq_sum_card_filter_fiber
    {α : Type u} {κ : Type v}
    [DecidableEq α] [Fintype κ] [DecidableEq κ]
    (A : Finset α) (key : α → κ) :
    A.card = ∑ k : κ, (A.filter fun a ↦ key a = k).card := by
  classical
  calc
    A.card = ∑ a ∈ A, 1 := by simp
    _ = ∑ a ∈ A, ∑ k : κ, if key a = k then 1 else 0 := by
      apply Finset.sum_congr rfl
      intro a _ha
      simp
    _ = ∑ k : κ, ∑ a ∈ A, if key a = k then 1 else 0 := by
      rw [Finset.sum_comm]
    _ = ∑ k : κ, (A.filter fun a ↦ key a = k).card := by
      apply Finset.sum_congr rfl
      intro k _hk
      simp

/-- A scaled cardinality inequality proved in every key fiber sums with the
same constants globally. -/
theorem mul_card_le_mul_card_of_fiberwise
    {α : Type u} {κ : Type v}
    [DecidableEq α] [Fintype κ] [DecidableEq κ]
    (A B : Finset α) (key : α → κ) (M C : ℕ)
    (hcell : ∀ k : κ,
      M * (A.filter fun a ↦ key a = k).card ≤
        C * (B.filter fun a ↦ key a = k).card) :
    M * A.card ≤ C * B.card := by
  rw [card_eq_sum_card_filter_fiber A key,
    card_eq_sum_card_filter_fiber B key]
  rw [Finset.mul_sum, Finset.mul_sum]
  exact Finset.sum_le_sum fun k _hk ↦ hcell k

/-- Predicate-restricted form, convenient for ordinary degree at a fixed
vertex. -/
theorem mul_card_filter_le_mul_card_filter_of_fiberwise
    {α : Type u} {κ : Type v}
    [DecidableEq α] [Fintype κ] [DecidableEq κ]
    (A B : Finset α) (key : α → κ) (P : α → Prop) [DecidablePred P]
    (M C : ℕ)
    (hcell : ∀ k : κ,
      M * ((A.filter P).filter fun a ↦ key a = k).card ≤
        C * ((B.filter P).filter fun a ↦ key a = k).card) :
    M * (A.filter P).card ≤ C * (B.filter P).card :=
  mul_card_le_mul_card_of_fiberwise
    (A.filter P) (B.filter P) key M C hcell

end WeightedEdgeColoring
