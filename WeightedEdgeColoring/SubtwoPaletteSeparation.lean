import Mathlib.Analysis.LocallyConvex.Separation
import Mathlib.Algebra.BigOperators.Group.Finset.Pi
import Mathlib.Tactic

/-!
# Nonnegative prices suffice for local palette feasibility

The five-vertex proof tests demands against nonnegative prices. This file
proves the separation argument justifying that restriction, for a closed
convex family of nonnegative vectors closed under coordinatewise deletion.
It does not assume or assert the global weighted-coloring theorem.
-/

open scoped BigOperators

namespace WeightedEdgeColoring.Subtwo

variable {I : Type*} [Fintype I] [DecidableEq I]

/-- A family of nonnegative demand vectors closed under deleting demand. -/
def NonnegativeDownwardClosed (S : Set (I → ℝ)) : Prop :=
  (∀ x ∈ S, ∀ i, 0 ≤ x i) ∧
    ∀ x ∈ S, ∀ y : I → ℝ,
      (∀ i, 0 ≤ y i) → (∀ i, y i ≤ x i) → y ∈ S

/-- A linear functional on a finite coordinate space is a coordinate price
sum. -/
theorem linearMap_eq_priceSum (f : (I → ℝ) →ₗ[ℝ] ℝ) (x : I → ℝ) :
    f x = ∑ i, f (Pi.single i 1) * x i := by
  have hx : x = ∑ i, x i • (Pi.single i 1 : I → ℝ) := by
    funext j
    simp [Finset.sum_apply, Pi.single_apply]
  conv_lhs => rw [hx]
  rw [map_sum]
  apply Finset.sum_congr rfl
  intro i _
  simp [mul_comm]

/-- Testing every nonnegative price is enough to establish feasibility.
The proof uses ordinary Hahn--Banach separation, then deletes coordinates
whose separating price is negative. -/
theorem mem_of_nonnegative_price_tests
    {S : Set (I → ℝ)} (hconvex : Convex ℝ S) (hclosed : IsClosed S)
    (hdown : NonnegativeDownwardClosed S) {d : I → ℝ}
    (hd : ∀ i, 0 ≤ d i)
    (htest : ∀ p : I → ℝ, (∀ i, 0 ≤ p i) →
      ∃ y ∈ S, (∑ i, p i * d i) ≤ ∑ i, p i * y i) : d ∈ S := by
  by_contra hnot
  obtain ⟨f, u, hfu, huf⟩ :=
    geometric_hahn_banach_closed_point hconvex hclosed hnot
  let a : I → ℝ := fun i ↦ f (Pi.single i 1)
  let p : I → ℝ := fun i ↦ max (a i) 0
  obtain ⟨y, hy, hdy⟩ := htest p (fun i ↦ le_max_right _ _)
  let z : I → ℝ := fun i ↦ if 0 ≤ a i then y i else 0
  have hz : z ∈ S := hdown.2 y hy z
    (fun i ↦ by dsimp [z]; split_ifs <;> [exact hdown.1 y hy i; rfl])
    (fun i ↦ by dsimp [z]; split_ifs <;> [rfl; exact hdown.1 y hy i])
  have hfz : f z = ∑ i, p i * y i := by
    change f.toLinearMap z = _
    rw [linearMap_eq_priceSum f.toLinearMap]
    apply Finset.sum_congr rfl
    intro i _
    change a i * z i = p i * y i
    by_cases hi : 0 ≤ a i
    · simp [z, p, hi]
    · simp [z, p, hi, max_eq_right (le_of_not_ge hi)]
  have hfd : f d ≤ ∑ i, p i * d i := by
    change f.toLinearMap d ≤ _
    rw [linearMap_eq_priceSum f.toLinearMap]
    exact Finset.sum_le_sum fun i _ ↦
      mul_le_mul_of_nonneg_right (le_max_left (a i) 0) (hd i)
  have hcontra : f d ≤ f z := by rw [hfz]; exact hfd.trans hdy
  exact (hcontra.trans_lt (hfu z hz)).not_gt huf

/-- The exact support-function characterization used for a local palette. -/
theorem mem_iff_nonnegative_price_tests
    {S : Set (I → ℝ)} (hconvex : Convex ℝ S) (hclosed : IsClosed S)
    (hdown : NonnegativeDownwardClosed S) {d : I → ℝ}
    (hd : ∀ i, 0 ≤ d i) :
    d ∈ S ↔ ∀ p : I → ℝ, (∀ i, 0 ≤ p i) →
      ∃ y ∈ S, (∑ i, p i * d i) ≤ ∑ i, p i * y i := by
  constructor
  · intro h p _
    exact ⟨d, h, le_rfl⟩
  · exact mem_of_nonnegative_price_tests hconvex hclosed hdown hd

end WeightedEdgeColoring.Subtwo
