import WeightedEdgeColoring.FiniteFractionalPatternCover
import Mathlib.Tactic

/-!
# Fractional packing of items heavier than one half

If every item has weight greater than one half, a feasible one-bin pattern
contains at most one item in total.  Consequently every fractional pattern
cover has cost at least the number of indexed items.
-/

open scoped BigOperators

namespace WeightedEdgeColoring
namespace BinPackingInstance

noncomputable section

universe u

variable (B : BinPackingInstance.{u})

namespace Pattern

/-- Total number of item copies in a one-bin pattern. -/
def totalMultiplicity (p : B.Pattern) : ℕ :=
  ∑ i : B.Item, p.multiplicity i

/-- A pattern of items all heavier than one half contains at most one copy
in total. -/
theorem totalMultiplicity_le_one_of_half_lt
    (hhalf : ∀ i, (1 / 2 : ℝ) < B.weight i)
    (p : B.Pattern) :
    p.totalMultiplicity ≤ 1 := by
  by_contra hnot
  have htwo : 2 ≤ p.totalMultiplicity := by omega
  have hposNat : 0 < ∑ i : B.Item, p.multiplicity i := by
    exact lt_of_lt_of_le (by norm_num) htwo
  have hnonnegNat : ∀ i ∈ (Finset.univ : Finset B.Item),
      0 ≤ p.multiplicity i := by
    intro i hi
    omega
  obtain ⟨i0, _hi0, hmi0⟩ :=
    (Finset.sum_pos_iff_of_nonneg hnonnegNat).mp hposNat
  have hpoint : ∀ i : B.Item,
      (p.multiplicity i : ℝ) / 2 ≤
        (p.multiplicity i : ℝ) * B.weight i := by
    intro i
    have hm : 0 ≤ (p.multiplicity i : ℝ) := Nat.cast_nonneg _
    nlinarith [hhalf i]
  have hstrictPoint :
      (p.multiplicity i0 : ℝ) / 2 <
        (p.multiplicity i0 : ℝ) * B.weight i0 := by
    have hm : 0 < (p.multiplicity i0 : ℝ) := by exact_mod_cast hmi0
    nlinarith [hhalf i0]
  have hstrict :
      (∑ i : B.Item, (p.multiplicity i : ℝ) / 2) <
        ∑ i : B.Item, (p.multiplicity i : ℝ) * B.weight i := by
    exact Finset.sum_lt_sum
      (fun i _hi ↦ hpoint i)
      ⟨i0, Finset.mem_univ i0, hstrictPoint⟩
  have hleft :
      (1 : ℝ) ≤ ∑ i : B.Item, (p.multiplicity i : ℝ) / 2 := by
    rw [← Finset.sum_div]
    have htwoReal : (2 : ℝ) ≤
        ∑ i : B.Item, (p.multiplicity i : ℝ) := by
      exact_mod_cast htwo
    linarith
  linarith [p.capacity]

end Pattern

namespace FractionalPatternCover

/-- Fractional cover cost dominates the number of items when every item is
heavier than one half. -/
theorem card_le_cost_of_half_lt
    (hhalf : ∀ i, (1 / 2 : ℝ) < B.weight i)
    (C : B.FractionalPatternCover) :
    (Fintype.card B.Item : ℝ) ≤ C.cost := by
  calc
    (Fintype.card B.Item : ℝ) = ∑ _i : B.Item, (1 : ℝ) := by simp
    _ ≤ ∑ i : B.Item, C.coverage i := by
      exact Finset.sum_le_sum fun i _hi ↦ C.one_le_coverage i
    _ = ∑ p ∈ C.coeff.support,
          C.coeff p * (∑ i : B.Item, (p.multiplicity i : ℝ)) := by
      simp only [coverage, Finset.mul_sum]
      rw [Finset.sum_comm]
    _ ≤ ∑ p ∈ C.coeff.support, C.coeff p * 1 := by
      exact Finset.sum_le_sum fun p _hp ↦
        mul_le_mul_of_nonneg_left
          (by
            have hnat := p.totalMultiplicity_le_one_of_half_lt B hhalf
            unfold Pattern.totalMultiplicity at hnat
            exact_mod_cast hnat)
          (C.coeff_nonneg p)
    _ = C.cost := by simp [cost]

end FractionalPatternCover

end

end BinPackingInstance
end WeightedEdgeColoring
