import WeightedEdgeColoring.BinPacking

/-! Finite indexed presentations of fractional pattern covers. -/

open scoped BigOperators

namespace WeightedEdgeColoring
namespace BinPackingInstance.FractionalPatternCover

noncomputable section

universe u v

variable {B : BinPackingInstance.{u}}
variable {J : Type v} [Fintype J] [DecidableEq J]

/-- A chosen fractional pattern cover attains the minimum when its cost is no
larger than the cost of every other cover.  Keeping the witness itself avoids
introducing an infimum or an attainment axiom. -/
def IsMinimumCost (C : B.FractionalPatternCover) : Prop :=
  ∀ D : B.FractionalPatternCover, C.cost ≤ D.cost

/-- Aggregate a finitely indexed family of weighted patterns into the
finite-support representation used by `FractionalPatternCover`. -/
def ofFinitePatterns (pattern : J → B.Pattern) (mass : J → ℝ)
    (mass_nonneg : ∀ j, 0 ≤ mass j)
    (covers : ∀ i : B.Item,
      1 ≤ ∑ j : J, mass j * (pattern j).multiplicity i) :
    B.FractionalPatternCover := by
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
    change 1 ≤ coeff.sum fun p c ↦ c * (p.multiplicity i : ℝ)
    dsimp [coeff]
    rw [← Finsupp.sum_finset_sum_index]
    · simpa using covers i
    · intro p
      simp
    · intro p c d
      simp [add_mul]

theorem ofFinitePatterns_cost (pattern : J → B.Pattern) (mass : J → ℝ)
    (mass_nonneg : ∀ j, 0 ≤ mass j)
    (covers : ∀ i : B.Item,
      1 ≤ ∑ j : J, mass j * (pattern j).multiplicity i) :
    (ofFinitePatterns pattern mass mass_nonneg covers).cost = ∑ j : J, mass j := by
  classical
  change ((∑ j : J, Finsupp.single (pattern j) (mass j)).sum
    fun _ c ↦ c) = ∑ j : J, mass j
  rw [← Finsupp.sum_finset_sum_index]
  · simp
  · simp
  · intro _ _ _
    rfl

end

end BinPackingInstance.FractionalPatternCover
end WeightedEdgeColoring
