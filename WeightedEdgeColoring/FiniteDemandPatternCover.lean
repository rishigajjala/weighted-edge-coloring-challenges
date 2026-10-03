import WeightedEdgeColoring.FiniteExactDemandFloorRemainderBound

/-!
# Fractional pattern covers with an arbitrary integral demand

For linear grouping we need a cover whose coordinates are the rounded
groups.  A group can contain many physical items, so its right-hand side is
an arbitrary natural number.  Equality is unnecessary: after flooring the
pattern coefficients we keep only as many occurrences of each group as its
demand asks for.

This file supplies that small variant of the configuration LP.  Flooring
never increases the number of packets, and the uncovered demand is bounded
only by the finite pattern type.  These are the two facts needed after
linear grouping has reduced a parallel bundle to a fixed number of rounded
sizes.
-/

open scoped BigOperators

namespace WeightedEdgeColoring
namespace BinPackingInstance

noncomputable section

universe u

variable (B : BinPackingInstance.{u})

/-- A nonnegative fractional combination of feasible one-bin patterns that
covers an arbitrary natural demand vector. -/
structure DemandPatternCover (demand : B.Item → ℕ) where
  coeff : B.Pattern →₀ ℝ
  coeff_nonneg : ∀ p, 0 ≤ coeff p
  covers : ∀ i : B.Item,
    (demand i : ℝ) ≤
      ∑ p ∈ coeff.support, coeff p * (p.multiplicity i : ℝ)

namespace DemandPatternCover

variable {B : BinPackingInstance.{u}} {demand : B.Item → ℕ}

/-- Total fractional number of bins. -/
def cost (C : B.DemandPatternCover demand) : ℝ :=
  ∑ p ∈ C.coeff.support, C.coeff p

theorem cost_nonneg (C : B.DemandPatternCover demand) : 0 ≤ C.cost := by
  exact Finset.sum_nonneg fun p _hp ↦ C.coeff_nonneg p

theorem sum_coeff_eq_cost (C : B.DemandPatternCover demand) :
    (∑ p : B.Pattern, C.coeff p) = C.cost := by
  symm
  exact Finsupp.sum_fintype C.coeff (fun _ c ↦ c) (by simp)

/-- Package finitely many named patterns and masses. -/
def ofFinitePatterns {J : Type*} [Fintype J] [DecidableEq J]
    (pattern : J → B.Pattern) (mass : J → ℝ)
    (mass_nonneg : ∀ j, 0 ≤ mass j)
    (covers : ∀ i : B.Item,
      (demand i : ℝ) ≤
        ∑ j : J, mass j * ((pattern j).multiplicity i : ℝ)) :
    B.DemandPatternCover demand := by
  classical
  let coeff : B.Pattern →₀ ℝ :=
    ∑ j : J, Finsupp.single (pattern j) (mass j)
  refine
    { coeff := coeff
      coeff_nonneg := ?_
      covers := ?_ }
  · intro p
    calc
      0 ≤ ∑ j : J, (Finsupp.single (pattern j) (mass j)) p := by
        exact Finset.sum_nonneg fun j _hj ↦ by
          by_cases h : pattern j = p
          · simp [Finsupp.single_apply, h, mass_nonneg j]
          · simp [Finsupp.single_apply, h]
      _ = coeff p := by
        dsimp [coeff]
        simpa using (map_sum (Finsupp.applyAddHom p)
          (fun j ↦ Finsupp.single (pattern j) (mass j)) Finset.univ).symm
  · intro i
    change (demand i : ℝ) ≤
      coeff.sum (fun p c ↦ c * (p.multiplicity i : ℝ))
    dsimp [coeff]
    rw [← Finsupp.sum_finset_sum_index]
    · simpa using covers i
    · intro p
      simp
    · intro p c e
      simp [add_mul]

theorem ofFinitePatterns_cost {J : Type*} [Fintype J] [DecidableEq J]
    (pattern : J → B.Pattern) (mass : J → ℝ)
    (mass_nonneg : ∀ j, 0 ≤ mass j)
    (covers : ∀ i : B.Item,
      (demand i : ℝ) ≤
        ∑ j : J, mass j * ((pattern j).multiplicity i : ℝ)) :
    (ofFinitePatterns pattern mass mass_nonneg covers).cost =
      ∑ j : J, mass j := by
  classical
  change ((∑ j : J, Finsupp.single (pattern j) (mass j)).sum
    fun _ c ↦ c) = ∑ j : J, mass j
  rw [← Finsupp.sum_finset_sum_index]
  · simp
  · simp
  · intro _ _ _
    rfl

/-- An ordinary unit-demand fractional cover is a demand cover. -/
def ofFractionalPatternCover (C : B.FractionalPatternCover) :
    B.DemandPatternCover (fun _ ↦ 1) where
  coeff := C.coeff
  coeff_nonneg := C.coeff_nonneg
  covers := fun i ↦ by simpa using C.one_le_coverage i

@[simp] theorem ofFractionalPatternCover_cost
    (C : B.FractionalPatternCover) :
    (DemandPatternCover.ofFractionalPatternCover C).cost = C.cost := rfl

/-- Number of full packet copies obtained by flooring every coefficient. -/
def floorPacketCount (C : B.DemandPatternCover demand) : ℕ :=
  ∑ p : B.Pattern, Nat.floor (C.coeff p)

/-- Labelled full packet copies. -/
abbrev FloorPacket (C : B.DemandPatternCover demand) :=
  Σ p : B.Pattern, Fin (Nat.floor (C.coeff p))

@[simp] theorem card_floorPacket (C : B.DemandPatternCover demand) :
    Fintype.card C.FloorPacket = C.floorPacketCount := by
  simp [FloorPacket, floorPacketCount]

/-- Demand supplied by all integral coefficient floors before capping it at
the requested demand. -/
def floorCoveredDemand (C : B.DemandPatternCover demand)
    (i : B.Item) : ℕ :=
  ∑ p : B.Pattern, Nat.floor (C.coeff p) * p.multiplicity i

/-- The number of occurrences of coordinate `i` that we actually retain. -/
def retainedDemand (C : B.DemandPatternCover demand) (i : B.Item) : ℕ :=
  min (demand i) (C.floorCoveredDemand i)

/-- Demand left after capping the floored occurrences at the requested
amount. -/
def floorResidualDemand (C : B.DemandPatternCover demand)
    (i : B.Item) : ℕ :=
  demand i - C.retainedDemand i

theorem retainedDemand_le_demand (C : B.DemandPatternCover demand)
    (i : B.Item) : C.retainedDemand i ≤ demand i :=
  min_le_left _ _

theorem retainedDemand_le_floorCoveredDemand
    (C : B.DemandPatternCover demand) (i : B.Item) :
    C.retainedDemand i ≤ C.floorCoveredDemand i :=
  min_le_right _ _

/-- Flooring creates no more packets than the fractional cost. -/
theorem floorPacketCount_cast_le_cost
    (C : B.DemandPatternCover demand) :
    (C.floorPacketCount : ℝ) ≤ C.cost := by
  rw [floorPacketCount]
  push_cast
  calc
    (∑ p : B.Pattern, (Nat.floor (C.coeff p) : ℝ)) ≤
        ∑ p : B.Pattern, C.coeff p := by
      exact Finset.sum_le_sum fun p _hp ↦
        Nat.floor_le (C.coeff_nonneg p)
    _ = C.cost := C.sum_coeff_eq_cost

/-- Before subtraction, demand is bounded by the floored coverage plus one
copy of every pattern multiplicity. -/
theorem demand_le_floorCoveredDemand_add_sum_pattern_multiplicity
    (C : B.DemandPatternCover demand) (i : B.Item) :
    demand i ≤ C.floorCoveredDemand i +
      ∑ p : B.Pattern, p.multiplicity i := by
  have hreal :
      (demand i : ℝ) ≤
        (C.floorCoveredDemand i : ℝ) +
          ∑ p : B.Pattern, (p.multiplicity i : ℝ) := by
    calc
      (demand i : ℝ) ≤
          ∑ p ∈ C.coeff.support,
            C.coeff p * (p.multiplicity i : ℝ) := C.covers i
      _ = ∑ p : B.Pattern,
            C.coeff p * (p.multiplicity i : ℝ) := by
        exact Finsupp.sum_fintype C.coeff
          (fun p c ↦ c * (p.multiplicity i : ℝ)) (by simp)
      _ ≤ ∑ p : B.Pattern,
          ((Nat.floor (C.coeff p) : ℝ) + 1) *
            (p.multiplicity i : ℝ) := by
        apply Finset.sum_le_sum
        intro p _hp
        exact mul_le_mul_of_nonneg_right
          (Nat.lt_floor_add_one (C.coeff p)).le (Nat.cast_nonneg _)
      _ = (C.floorCoveredDemand i : ℝ) +
          ∑ p : B.Pattern, (p.multiplicity i : ℝ) := by
        rw [floorCoveredDemand, Nat.cast_sum]
        push_cast
        rw [← Finset.sum_add_distrib]
        apply Finset.sum_congr rfl
        intro p _hp
        ring
  exact_mod_cast hreal

/-- Uncovered demand in one coordinate is bounded independently of the
original demand. -/
theorem floorResidualDemand_le_sum_pattern_multiplicity
    (C : B.DemandPatternCover demand) (i : B.Item) :
    C.floorResidualDemand i ≤
      ∑ p : B.Pattern, p.multiplicity i := by
  have h := C.demand_le_floorCoveredDemand_add_sum_pattern_multiplicity i
  unfold floorResidualDemand retainedDemand
  by_cases hcov : demand i ≤ C.floorCoveredDemand i
  · simp [min_eq_left hcov]
  · rw [min_eq_right (Nat.le_of_not_ge hcov)]
    omega

/-- Total uncovered demand when every pattern coordinate is at most `T`. -/
theorem sum_floorResidualDemand_le_card_mul_patternCard_mul
    (C : B.DemandPatternCover demand) (T : ℕ)
    (hmult : ∀ p : B.Pattern, ∀ i : B.Item,
      p.multiplicity i ≤ T) :
    (∑ i : B.Item, C.floorResidualDemand i) ≤
      Fintype.card B.Item * (Fintype.card B.Pattern * T) := by
  calc
    (∑ i : B.Item, C.floorResidualDemand i) ≤
        ∑ _i : B.Item, Fintype.card B.Pattern * T := by
      apply Finset.sum_le_sum
      intro i _hi
      calc
        C.floorResidualDemand i ≤
            ∑ p : B.Pattern, p.multiplicity i :=
          C.floorResidualDemand_le_sum_pattern_multiplicity i
        _ ≤ ∑ _p : B.Pattern, T := by
          exact Finset.sum_le_sum fun p _hp ↦ hmult p i
        _ = Fintype.card B.Pattern * T := by simp
    _ = Fintype.card B.Item * (Fintype.card B.Pattern * T) := by simp

/-- Concrete bound when every item has harmonic multiplicity at most `T`. -/
theorem sum_floorResidualDemand_le_card_mul_succ_pow_card_mul
    (C : B.DemandPatternCover demand) (T : ℕ)
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

end DemandPatternCover

end

end BinPackingInstance
end WeightedEdgeColoring

#print axioms WeightedEdgeColoring.BinPackingInstance.DemandPatternCover.floorPacketCount_cast_le_cost
#print axioms WeightedEdgeColoring.BinPackingInstance.DemandPatternCover.sum_floorResidualDemand_le_card_mul_succ_pow_card_mul
