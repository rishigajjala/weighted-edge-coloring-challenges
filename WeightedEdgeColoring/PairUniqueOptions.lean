import WeightedEdgeColoring.QuantizedOptions

open scoped BigOperators

namespace WeightedEdgeColoring

/-!
# Pair-unique option systems

In the simple-graph application, two distinct concrete endpoint slots can
belong to at most one base option: the slots identify their endpoints and
the simple graph has at most one edge between them.  This small interface
turns that structural fact into the required replicated pair-codegree bound.
-/

noncomputable section

universe u v w

namespace RankThreeOptionSystem

variable {Job : Type u} {Slot : Type v} {Option : Type w}
  [Fintype Job] [Fintype Slot] [Fintype Option]
  [DecidableEq Job] [DecidableEq Slot] [DecidableEq Option]

/-- Every two distinct slots determine at most one base option. -/
def PairUnique (H : RankThreeOptionSystem Job Slot Option) : Prop :=
  ∀ ⦃s t : Slot⦄, s ≠ t → ∀ ⦃o p : Option⦄,
    s ∈ H.slots o → t ∈ H.slots o →
    s ∈ H.slots p → t ∈ H.slots p → o = p

/-- The family of base options using a fixed distinct slot pair has at most
one member. -/
theorem card_pairSupport_le_one
    (H : RankThreeOptionSystem Job Slot Option) (hunique : H.PairUnique)
    {s t : Slot} (hst : s ≠ t) :
    ((Finset.univ : Finset Option).filter fun o ↦
      s ∈ H.slots o ∧ t ∈ H.slots o).card ≤ 1 := by
  classical
  rw [Finset.card_le_one]
  intro o ho p hp
  have ho' := (Finset.mem_filter.mp ho).2
  have hp' := (Finset.mem_filter.mp hp).2
  exact hunique hst ho'.1 ho'.2 hp'.1 hp'.2

/-- Hence the unreplicated pair-codegree is at most one. -/
theorem slotPairCodegree_le_one
    (H : RankThreeOptionSystem Job Slot Option) (hunique : H.PairUnique)
    {s t : Slot} (hst : s ≠ t) :
    H.slotPairCodegree s t ≤ 1 := by
  exact H.card_pairSupport_le_one hunique hst

/-- If every base option has mass at most `tau`, floor replication gives
pair-codegree at most `N*tau` for every distinct slot pair. -/
theorem quantized_slotPairCodegree_le
    (H : RankThreeOptionSystem Job Slot Option) (hunique : H.PairUnique)
    (N : ℕ) (x : Option → ℝ) (tau : ℝ)
    (htau0 : 0 ≤ tau) (hx0 : ∀ o, 0 ≤ x o)
    (hxtau : ∀ o, x o ≤ tau)
    {s t : Slot} (hst : s ≠ t) :
    (((H.quantized N x).slotPairCodegree s t : ℕ) : ℝ) ≤
      (N : ℝ) * tau := by
  classical
  let A : Finset Option := (Finset.univ : Finset Option).filter fun o ↦
    s ∈ H.slots o ∧ t ∈ H.slots o
  have hA : A.card ≤ 1 := H.card_pairSupport_le_one hunique hst
  rw [H.quantized_slotPairCodegree, Nat.cast_sum]
  have hrewrite :
      (∑ o, ((if s ∈ H.slots o ∧ t ∈ H.slots o then
          quantizedMultiplicity N (x o) else 0 : ℕ) : ℝ)) =
        ∑ o ∈ A, (quantizedMultiplicity N (x o) : ℝ) := by
    simp only [Nat.cast_ite, Nat.cast_zero]
    rw [← Finset.sum_filter]
  rw [hrewrite]
  calc
    (∑ o ∈ A, (quantizedMultiplicity N (x o) : ℝ)) ≤
        ∑ _o ∈ A, (N : ℝ) * tau := by
      apply Finset.sum_le_sum
      intro o _ho
      calc
        (quantizedMultiplicity N (x o) : ℝ) ≤ (N : ℝ) * x o :=
          Nat.floor_le (mul_nonneg (Nat.cast_nonneg N) (hx0 o))
        _ ≤ (N : ℝ) * tau :=
          mul_le_mul_of_nonneg_left (hxtau o) (Nat.cast_nonneg N)
    _ = (A.card : ℝ) * ((N : ℝ) * tau) := by simp
    _ ≤ 1 * ((N : ℝ) * tau) := by
      exact mul_le_mul_of_nonneg_right (by exact_mod_cast hA)
        (mul_nonneg (Nat.cast_nonneg N) htau0)
    _ = (N : ℝ) * tau := one_mul _

end RankThreeOptionSystem

end

end WeightedEdgeColoring
