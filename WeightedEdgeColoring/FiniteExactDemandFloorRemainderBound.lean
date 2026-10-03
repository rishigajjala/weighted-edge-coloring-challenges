import WeightedEdgeColoring.BPGraphExactDemandBundlePacking
import WeightedEdgeColoring.FiniteExactDemandHarmonicMinimum

/-!
# Uniform remainder bound after flooring an exact-demand cover

If an exact-demand bin-packing instance has `D` item types and every
one-bin pattern uses at most `T` copies of each type, flooring all pattern
coefficients leaves only a bounded number of item occurrences.  The bound
depends on `D` and `T`, not on the original demand.  This is the finite-type
counting fact needed after linear grouping reduces every parallel bundle to
a fixed number of rounded weight types.
-/

open scoped BigOperators

namespace WeightedEdgeColoring
namespace BinPackingInstance

noncomputable section

universe u

variable {B : BinPackingInstance.{u}} {demand : B.Item → ℕ}

namespace ExactDemandPatternCover

/-- The demand of one type not represented by the integral coefficient
floors. -/
def floorResidualDemand (C : B.ExactDemandPatternCover demand)
    (i : B.Item) : ℕ :=
  demand i - C.floorCoveredDemand i

/-- Before subtraction, the original demand is at most the floor-covered
demand plus one copy of each pattern's multiplicity. -/
theorem demand_le_floorCoveredDemand_add_sum_pattern_multiplicity
    (C : B.ExactDemandPatternCover demand) (i : B.Item) :
    demand i ≤ C.floorCoveredDemand i +
      ∑ p : B.Pattern, p.multiplicity i := by
  have hreal :
      (demand i : ℝ) ≤
        (C.floorCoveredDemand i : ℝ) +
          ∑ p : B.Pattern, (p.multiplicity i : ℝ) := by
    rw [← C.sum_coeff_mul_multiplicity_eq i]
    rw [floorCoveredDemand, Nat.cast_sum]
    push_cast
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_le_sum
    intro p _hp
    have hcoeff :
        C.coeff p ≤ (Nat.floor (C.coeff p) : ℝ) + 1 :=
      (Nat.lt_floor_add_one (C.coeff p)).le
    have hmul := mul_le_mul_of_nonneg_right hcoeff
      (Nat.cast_nonneg (p.multiplicity i))
    nlinarith
  exact_mod_cast hreal

/-- The residual demand of one item type is bounded by the sum of that
coordinate over all feasible patterns. -/
theorem floorResidualDemand_le_sum_pattern_multiplicity
    (C : B.ExactDemandPatternCover demand) (i : B.Item) :
    C.floorResidualDemand i ≤
      ∑ p : B.Pattern, p.multiplicity i := by
  have h := C.demand_le_floorCoveredDemand_add_sum_pattern_multiplicity i
  unfold floorResidualDemand
  omega

/-- If every pattern coordinate is at most `T`, the residual demand of one
item type is at most `|Pattern| T`. -/
theorem floorResidualDemand_le_patternCard_mul
    (C : B.ExactDemandPatternCover demand) (T : ℕ)
    (hmult : ∀ p : B.Pattern, ∀ i : B.Item, p.multiplicity i ≤ T)
    (i : B.Item) :
    C.floorResidualDemand i ≤ Fintype.card B.Pattern * T := by
  calc
    C.floorResidualDemand i ≤
        ∑ p : B.Pattern, p.multiplicity i :=
      C.floorResidualDemand_le_sum_pattern_multiplicity i
    _ ≤ ∑ _p : B.Pattern, T := by
      exact Finset.sum_le_sum fun p _hp ↦ hmult p i
    _ = Fintype.card B.Pattern * T := by simp

/-- Summing over all item types gives a demand-independent bound on all
unassigned occurrences. -/
theorem sum_floorResidualDemand_le_card_mul_patternCard_mul
    (C : B.ExactDemandPatternCover demand) (T : ℕ)
    (hmult : ∀ p : B.Pattern, ∀ i : B.Item, p.multiplicity i ≤ T) :
    (∑ i : B.Item, C.floorResidualDemand i) ≤
      Fintype.card B.Item * (Fintype.card B.Pattern * T) := by
  calc
    (∑ i : B.Item, C.floorResidualDemand i) ≤
        ∑ _i : B.Item, Fintype.card B.Pattern * T := by
      exact Finset.sum_le_sum fun i _hi ↦
        C.floorResidualDemand_le_patternCard_mul T hmult i
    _ = Fintype.card B.Item * (Fintype.card B.Pattern * T) := by simp

end ExactDemandPatternCover

namespace Pattern

/-- If every harmonic multiplicity is at most `T`, then the finite pattern
type has at most `(T+1)^D` elements, where `D` is the number of item types. -/
theorem card_le_succ_pow_card_of_harmonicMultiplicity_le
    (B : BinPackingInstance.{u}) (T : ℕ)
    (hfloor : ∀ i : B.Item, Nat.floor (1 / B.weight i) ≤ T) :
    Fintype.card B.Pattern ≤ (T + 1) ^ Fintype.card B.Item := by
  have hcode :
      Fintype.card B.Pattern ≤
        Fintype.card (∀ i : B.Item,
          Fin (Nat.floor (1 / B.weight i) + 1)) :=
    Fintype.card_le_of_injective (Pattern.finiteCode B)
      (Pattern.finiteCode_injective B)
  calc
    Fintype.card B.Pattern ≤
        Fintype.card (∀ i : B.Item,
          Fin (Nat.floor (1 / B.weight i) + 1)) := hcode
    _ = ∏ i : B.Item, (Nat.floor (1 / B.weight i) + 1) := by simp
    _ ≤ ∏ _i : B.Item, (T + 1) := by
      apply Finset.prod_le_prod
      · intro i _hi
        exact Nat.zero_le _
      · intro i _hi
        exact Nat.add_le_add_right (hfloor i) 1
    _ = (T + 1) ^ Fintype.card B.Item := by simp

end Pattern

namespace ExactDemandPatternCover

/-- Concrete finite-type remainder bound using only a uniform harmonic
multiplicity bound. -/
theorem sum_floorResidualDemand_le_card_mul_succ_pow_card_mul
    (C : B.ExactDemandPatternCover demand) (T : ℕ)
    (hfloor : ∀ i : B.Item, Nat.floor (1 / B.weight i) ≤ T) :
    (∑ i : B.Item, C.floorResidualDemand i) ≤
      Fintype.card B.Item *
        ((T + 1) ^ Fintype.card B.Item * T) := by
  have hmult : ∀ p : B.Pattern, ∀ i : B.Item,
      p.multiplicity i ≤ T := by
    intro p i
    exact (Pattern.multiplicity_le_floor B p i).trans (hfloor i)
  calc
    (∑ i : B.Item, C.floorResidualDemand i) ≤
        Fintype.card B.Item * (Fintype.card B.Pattern * T) :=
      C.sum_floorResidualDemand_le_card_mul_patternCard_mul T hmult
    _ ≤ Fintype.card B.Item *
        ((T + 1) ^ Fintype.card B.Item * T) := by
      gcongr
      exact Pattern.card_le_succ_pow_card_of_harmonicMultiplicity_le
        B T hfloor

end ExactDemandPatternCover

end

end BinPackingInstance
end WeightedEdgeColoring
