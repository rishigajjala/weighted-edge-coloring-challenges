import WeightedEdgeColoring.FiniteBinPackingPatterns
import WeightedEdgeColoring.FiniteFractionalPatternCover
import Mathlib

/-!
# Minimum finite fractional pattern covers

The set of one-bin patterns is finite.  We therefore minimize the fractional
cover cost on a compact finite-dimensional box.  This supplies the minimum
cost witnesses consumed by the two-bag extraction in the general multigraph
argument; no attainment assumption is needed.
-/

open scoped BigOperators

namespace WeightedEdgeColoring
namespace BinPackingInstance

noncomputable section

universe u

variable (B : BinPackingInstance.{u})

namespace Pattern

/-- The empty one-bin pattern. -/
def zero : B.Pattern where
  multiplicity := fun _ ↦ 0
  capacity := by simp

/-- The one-bin pattern containing one copy of item `i`. -/
def singleton (i : B.Item) : B.Pattern where
  multiplicity := fun j ↦ if j = i then 1 else 0
  capacity := by
    classical
    simp [B.weight_le_one i]

@[simp] theorem singleton_multiplicity_self (i : B.Item) :
    (Pattern.singleton B i).multiplicity i = 1 := by
  simp [Pattern.singleton]

end Pattern

namespace FractionalPatternCover

/-- Cost of a coefficient vector indexed by all feasible patterns. -/
def coefficientCost (x : B.Pattern → ℝ) : ℝ :=
  ∑ p : B.Pattern, x p

/-- Coverage of item coordinate `i` by a coefficient vector. -/
def coefficientCoverage (x : B.Pattern → ℝ) (i : B.Item) : ℝ :=
  ∑ p : B.Pattern, x p * (p.multiplicity i : ℝ)

/-- A coefficient vector is a fractional pattern cover. -/
def CoefficientFeasible (x : B.Pattern → ℝ) : Prop :=
  (∀ p, 0 ≤ x p) ∧ (∀ i, 1 ≤ coefficientCoverage B x i)

/-- Every `Finsupp` cost equals the sum over the now-finite full pattern
type. -/
theorem sum_coeff_eq_cost (C : B.FractionalPatternCover) :
    (∑ p : B.Pattern, C.coeff p) = C.cost := by
  calc
    (∑ p : B.Pattern, C.coeff p) =
        C.coeff.sum (fun _ c ↦ c) := by
      symm
      exact Finsupp.sum_fintype C.coeff (fun _ c ↦ c) (by simp)
    _ = C.cost := rfl

/-- The full finite sum computes the coverage carried by a fractional
cover. -/
theorem sum_coeff_mul_eq_coverage (C : B.FractionalPatternCover)
    (i : B.Item) :
    (∑ p : B.Pattern, C.coeff p * (p.multiplicity i : ℝ)) =
      C.coverage i := by
  calc
    (∑ p : B.Pattern, C.coeff p * (p.multiplicity i : ℝ)) =
        C.coeff.sum (fun p c ↦ c * (p.multiplicity i : ℝ)) := by
      symm
      exact Finsupp.sum_fintype C.coeff
        (fun p c ↦ c * (p.multiplicity i : ℝ)) (by simp)
    _ = C.coverage i := rfl

/-- Turn a feasible full coefficient vector into a finite-support
fractional pattern cover. -/
def ofCoefficientFunction (x : B.Pattern → ℝ)
    (hx : CoefficientFeasible B x) :
    B.FractionalPatternCover := by
  let coeff : B.Pattern →₀ ℝ := Finsupp.equivFunOnFinite.symm x
  refine
    { coeff := coeff
      coeff_nonneg := ?_
      covers := ?_ }
  · intro p
    simpa [coeff] using hx.1 p
  · intro i
    calc
      1 ≤ coefficientCoverage B x i := hx.2 i
      _ = ∑ p : B.Pattern, coeff p * (p.multiplicity i : ℝ) := by
        simp [coefficientCoverage, coeff]
      _ = ∑ p ∈ coeff.support,
          coeff p * (p.multiplicity i : ℝ) := by
        symm
        exact Finsupp.sum_fintype coeff
          (fun p c ↦ c * (p.multiplicity i : ℝ)) (by simp)

@[simp] theorem ofCoefficientFunction_coeff (x : B.Pattern → ℝ)
    (hx : CoefficientFeasible B x)
    (p : B.Pattern) :
    (ofCoefficientFunction B x hx).coeff p = x p := by
  simp [ofCoefficientFunction]

theorem ofCoefficientFunction_cost (x : B.Pattern → ℝ)
    (hx : CoefficientFeasible B x) :
    (ofCoefficientFunction B x hx).cost = coefficientCost B x := by
  rw [← sum_coeff_eq_cost]
  simp [coefficientCost]

/-- The number of feasible one-bin patterns, used as a compact-box bound. -/
def patternCount : ℝ := Fintype.card B.Pattern

theorem one_le_patternCount : 1 ≤ patternCount B := by
  unfold patternCount
  exact_mod_cast (Fintype.card_pos_iff.mpr ⟨Pattern.zero B⟩)

/-- Feasible coefficient vectors inside a common compact box. -/
def boundedFeasibleSet : Set (B.Pattern → ℝ) :=
  Set.Icc (fun _ ↦ 0) (fun _ ↦ patternCount B) ∩
    {x | ∀ i, 1 ≤ coefficientCoverage B x i}

theorem continuous_coefficientCoverage (i : B.Item) :
    Continuous (fun x : B.Pattern → ℝ ↦
      coefficientCoverage B x i) := by
  unfold coefficientCoverage
  apply continuous_finset_sum
  intro p _hp
  exact (continuous_apply p).mul continuous_const

theorem continuous_coefficientCost :
    Continuous (coefficientCost B :
      (B.Pattern → ℝ) → ℝ) := by
  unfold coefficientCost
  apply continuous_finset_sum
  intro p _hp
  exact continuous_apply p

theorem isClosed_coverageSet :
    IsClosed {x : B.Pattern → ℝ |
      ∀ i, 1 ≤ coefficientCoverage B x i} := by
  rw [show {x : B.Pattern → ℝ |
      ∀ i, 1 ≤ coefficientCoverage B x i} =
      ⋂ i : B.Item,
        {x | (fun _ : B.Pattern → ℝ ↦ (1 : ℝ)) x ≤
          coefficientCoverage B x i} by
    ext x
    simp]
  apply isClosed_iInter
  intro i
  exact isClosed_le continuous_const
    (continuous_coefficientCoverage B i)

theorem isCompact_boundedFeasibleSet :
    IsCompact (boundedFeasibleSet B) := by
  unfold boundedFeasibleSet
  exact isCompact_Icc.inter_right
    (isClosed_coverageSet B)

/-- The constant-one coefficient vector covers every item and lies in the
compact box. -/
theorem one_mem_boundedFeasibleSet :
    (fun _ : B.Pattern ↦ (1 : ℝ)) ∈
      boundedFeasibleSet B := by
  constructor
  · constructor
    · intro p
      norm_num
    · intro p
      exact one_le_patternCount B
  · intro i
    unfold coefficientCoverage
    have hsingle :
        (1 : ℝ) ≤
          ((Pattern.singleton B i).multiplicity i : ℝ) := by simp
    calc
      (1 : ℝ) ≤ ((Pattern.singleton B i).multiplicity i : ℝ) := hsingle
      _ ≤ ∑ p : B.Pattern, (p.multiplicity i : ℝ) := by
        exact Finset.single_le_sum
          (f := fun p : B.Pattern ↦ (p.multiplicity i : ℝ))
          (fun p _hp ↦ Nat.cast_nonneg (p.multiplicity i))
          (Finset.mem_univ (Pattern.singleton B i))
      _ = ∑ p : B.Pattern,
          (1 : ℝ) * (p.multiplicity i : ℝ) := by simp

/-- Every finite bin-packing instance has an attained minimum-cost
fractional pattern cover. -/
theorem exists_minimumCost :
    ∃ C : B.FractionalPatternCover, C.IsMinimumCost := by
  obtain ⟨x, hx, hxmin⟩ :=
    (isCompact_boundedFeasibleSet B).exists_isMinOn
      ⟨_, one_mem_boundedFeasibleSet B⟩
      (continuous_coefficientCost B).continuousOn
  have hxfeasible : CoefficientFeasible B x := by
    refine ⟨?_, hx.2⟩
    intro p
    exact hx.1.1 p
  let C := ofCoefficientFunction B x hxfeasible
  refine ⟨C, ?_⟩
  intro D
  let y : B.Pattern → ℝ := fun p ↦ D.coeff p
  have hyfeasible : CoefficientFeasible B y := by
    constructor
    · intro p
      exact D.coeff_nonneg p
    · intro i
      calc
        1 ≤ D.coverage i := D.one_le_coverage i
        _ = coefficientCoverage B y i := by
          rw [← sum_coeff_mul_eq_coverage B D i]
          rfl
  have hycost : coefficientCost B y = D.cost := by
    exact sum_coeff_eq_cost B D
  have hCcost : C.cost = coefficientCost B x := by
    exact ofCoefficientFunction_cost B x hxfeasible
  by_cases hDsmall : D.cost ≤ patternCount B
  · have hybox : y ∈ boundedFeasibleSet B := by
      refine ⟨⟨hyfeasible.1, ?_⟩, hyfeasible.2⟩
      intro p
      calc
        y p ≤ ∑ q : B.Pattern, y q := by
          exact Finset.single_le_sum
            (fun q _hq ↦ hyfeasible.1 q) (Finset.mem_univ p)
        _ = D.cost := hycost
        _ ≤ patternCount B := hDsmall
    rw [hCcost]
    calc
      coefficientCost B x ≤ coefficientCost B y := hxmin hybox
      _ = D.cost := hycost
  · have honecost :
        coefficientCost B
            (fun _ : B.Pattern ↦ (1 : ℝ)) =
          patternCount B := by
      simp [coefficientCost, patternCount]
    have hxsmallRaw := hxmin (one_mem_boundedFeasibleSet B)
    change coefficientCost B x ≤
      coefficientCost B (fun _ : B.Pattern ↦ (1 : ℝ)) at hxsmallRaw
    have hxsmall : coefficientCost B x ≤ patternCount B := by
      calc
        coefficientCost B x ≤
            coefficientCost B (fun _ : B.Pattern ↦ (1 : ℝ)) := hxsmallRaw
        _ = patternCount B := honecost
    rw [hCcost]
    exact hxsmall.trans (lt_of_not_ge hDsmall).le

end FractionalPatternCover

end

end BinPackingInstance
end WeightedEdgeColoring
