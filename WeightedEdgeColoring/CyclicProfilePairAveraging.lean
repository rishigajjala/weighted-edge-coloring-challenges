import Mathlib.Algebra.BigOperators.Field
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.Fintype.EquivFin
import Mathlib.Data.Real.Basic
import Mathlib.Logic.Equiv.Fin.Rotate
import Mathlib.Tactic.FieldSimp

open scoped BigOperators

namespace WeightedEdgeColoring

/-!
# Averaging two finite words by cyclic shifts

If two words of the same positive length are placed on a circle, then every
ordered pair of positions occurs exactly once as one word is cyclically
shifted past the other.  Consequently, the sum of a pair cost over all
positions and all shifts is the full pair sum.  At least one shift therefore
has cost no larger than the average full-pair cost.

This elementary lemma is useful when two independently balanced profile
words must be synchronized across an edge.
-/

noncomputable section

universe u v

variable {A : Type u} {B : Type v}

/-- The cost of pairing two words after cyclically shifting the second word. -/
def cyclicPairCost {n : ℕ} (a : Fin n → A) (b : Fin n → B)
    (f : A → B → ℝ) (t : Fin n) : ℝ :=
  ∑ c : Fin n, f (a c) (b (c + t))

/-- For a fixed first position, cyclic addition runs through every second
position exactly once. -/
theorem sum_cyclic_add_left {n : ℕ} (c : Fin n)
    (g : Fin n → ℝ) :
    ∑ t : Fin n, g (c + t) = ∑ d : Fin n, g d := by
  simpa [finCycle_apply, add_comm] using (Equiv.sum_comp (finCycle c) g)

/-- Summing a pair cost over all cyclic shifts gives the full ordered-pair
sum.  Thus every pair of positions occurs exactly once. -/
theorem sum_cyclicPairCost {n : ℕ}
    (a : Fin n → A) (b : Fin n → B) (f : A → B → ℝ) :
    ∑ t : Fin n, cyclicPairCost a b f t =
      ∑ c : Fin n, ∑ d : Fin n, f (a c) (b d) := by
  classical
  unfold cyclicPairCost
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro c _hc
  exact sum_cyclic_add_left c (fun d ↦ f (a c) (b d))

/-- Some cyclic shift costs at most the average full-pair cost. -/
theorem exists_cyclicShift_cost_le_average {n : ℕ} (hn : 0 < n)
    (a : Fin n → A) (b : Fin n → B) (f : A → B → ℝ) :
    ∃ t : Fin n,
      cyclicPairCost a b f t ≤
        (∑ c : Fin n, ∑ d : Fin n, f (a c) (b d)) / (n : ℝ) := by
  classical
  letI : NeZero n := ⟨Nat.ne_of_gt hn⟩
  have hnR : (n : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hn)
  have hsum_le :
      (∑ t : Fin n, cyclicPairCost a b f t) ≤
        ∑ _t : Fin n,
          (∑ c : Fin n, ∑ d : Fin n, f (a c) (b d)) / (n : ℝ) := by
    rw [sum_cyclicPairCost]
    simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin,
      nsmul_eq_mul]
    field_simp
    exact le_rfl
  obtain ⟨t, _ht, hcost⟩ :=
    Finset.exists_le_of_sum_le (s := (Finset.univ : Finset (Fin n)))
      Finset.univ_nonempty hsum_le
  exact ⟨t, hcost⟩

end

end WeightedEdgeColoring
