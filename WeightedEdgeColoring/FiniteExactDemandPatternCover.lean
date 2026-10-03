import WeightedEdgeColoring.FiniteFractionalPatternCoverMinimum

/-!
# Finite exact-demand pattern covers

The usual configuration LP in `BinPacking` only asks that every item
coordinate be covered at least once.  Packet-count arguments need a slightly
different finite object: a prescribed natural multiplicity must be covered
exactly.  This file gives that object and proves that its minimum cost is
attained.  The proof uses the already established finiteness of the one-bin
pattern type and compact minimization in a finite-dimensional box.
-/

open scoped BigOperators

namespace WeightedEdgeColoring
namespace BinPackingInstance

noncomputable section

universe u

variable (B : BinPackingInstance.{u})

/-- A finite-support nonnegative combination of feasible patterns whose
coverage is exactly the prescribed count in every item coordinate. -/
structure ExactDemandPatternCover (demand : B.Item → ℕ) where
  coeff : B.Pattern →₀ ℝ
  coeff_nonneg : ∀ p, 0 ≤ coeff p
  covers_exact : ∀ i : B.Item,
    (∑ p ∈ coeff.support, coeff p * (p.multiplicity i : ℝ)) = demand i

namespace ExactDemandPatternCover

variable {B} {demand : B.Item → ℕ}

/-- Exact coverage of one demand coordinate. -/
def coverage (C : B.ExactDemandPatternCover demand) (i : B.Item) : ℝ :=
  ∑ p ∈ C.coeff.support, C.coeff p * (p.multiplicity i : ℝ)

/-- Total mass of the patterns in an exact-demand cover. -/
def cost (C : B.ExactDemandPatternCover demand) : ℝ :=
  ∑ p ∈ C.coeff.support, C.coeff p

@[simp] theorem coverage_eq (C : B.ExactDemandPatternCover demand)
    (i : B.Item) : C.coverage i = demand i :=
  C.covers_exact i

theorem cost_nonneg (C : B.ExactDemandPatternCover demand) : 0 ≤ C.cost := by
  exact Finset.sum_nonneg fun p _hp ↦ C.coeff_nonneg p

/-- Forget exactness when every prescribed coordinate is positive. -/
def toFractionalPatternCover (C : B.ExactDemandPatternCover demand)
    (hdemand : ∀ i, 1 ≤ demand i) : B.FractionalPatternCover where
  coeff := C.coeff
  coeff_nonneg := C.coeff_nonneg
  covers := fun i ↦ by
    rw [C.covers_exact i]
    exact_mod_cast hdemand i

@[simp] theorem toFractionalPatternCover_coeff
    (C : B.ExactDemandPatternCover demand) (hdemand : ∀ i, 1 ≤ demand i) :
    (C.toFractionalPatternCover hdemand).coeff = C.coeff := rfl

@[simp] theorem toFractionalPatternCover_cost
    (C : B.ExactDemandPatternCover demand) (hdemand : ∀ i, 1 ≤ demand i) :
    (C.toFractionalPatternCover hdemand).cost = C.cost := rfl

/-- A chosen exact-demand cover is minimum when it is no more expensive than
every other exact-demand cover for the same demand vector. -/
def IsMinimumCost (C : B.ExactDemandPatternCover demand) : Prop :=
  ∀ D : B.ExactDemandPatternCover demand, C.cost ≤ D.cost

/-- A labelled integral packing of an exact count demand.  Each labelled bin
is represented directly by its feasible one-bin pattern. -/
structure PackingCertificate (demand : B.Item → ℕ) (n : ℕ) where
  pattern : Fin n → B.Pattern
  covers_exact : ∀ i : B.Item,
    (∑ j : Fin n, (pattern j).multiplicity i) = demand i

/-- The exact count demand packs into `n` labelled bins. -/
def PacksInto (demand : B.Item → ℕ) (n : ℕ) : Prop :=
  Nonempty (PackingCertificate demand n)

/-- Aggregate finitely many named patterns into an exact-demand cover. -/
def ofFinitePatterns {J : Type*} [Fintype J] [DecidableEq J]
    (pattern : J → B.Pattern) (mass : J → ℝ)
    (mass_nonneg : ∀ j, 0 ≤ mass j)
    (covers : ∀ i : B.Item,
      (∑ j : J, mass j * (pattern j).multiplicity i) = demand i) :
    B.ExactDemandPatternCover demand := by
  classical
  let coeff : B.Pattern →₀ ℝ :=
    ∑ j : J, Finsupp.single (pattern j) (mass j)
  refine
    { coeff := coeff
      coeff_nonneg := ?_
      covers_exact := ?_ }
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
    change coeff.sum (fun p c ↦ c * (p.multiplicity i : ℝ)) = demand i
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
      (∑ j : J, mass j * (pattern j).multiplicity i) = demand i) :
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

/-- Give each labelled bin of an exact integral packing unit mass. -/
def PackingCertificate.toExactDemandPatternCover {n : ℕ}
    (P : PackingCertificate demand n) :
    B.ExactDemandPatternCover demand :=
  ofFinitePatterns P.pattern (fun _ : Fin n ↦ (1 : ℝ))
    (fun _ ↦ zero_le_one)
    (by
      intro i
      simpa using congrArg (fun k : ℕ ↦ (k : ℝ)) (P.covers_exact i))

@[simp] theorem PackingCertificate.toExactDemandPatternCover_cost {n : ℕ}
    (P : PackingCertificate demand n) :
    P.toExactDemandPatternCover.cost = n := by
  rw [PackingCertificate.toExactDemandPatternCover, ofFinitePatterns_cost]
  simp

/-- An exact integral packing yields an exact fractional cover of the same
cost. -/
theorem exists_cost_eq_of_packsInto {n : ℕ}
    (h : PacksInto demand n) :
    ∃ C : B.ExactDemandPatternCover demand, C.cost = n := by
  rcases h with ⟨P⟩
  exact ⟨P.toExactDemandPatternCover,
    P.toExactDemandPatternCover_cost⟩

/-- Cover every demanded copy in its own singleton pattern. -/
def singletonCover (B : BinPackingInstance.{u}) (demand : B.Item → ℕ) :
    B.ExactDemandPatternCover demand :=
  ofFinitePatterns (fun i ↦ Pattern.singleton B i)
    (fun i ↦ (demand i : ℝ))
    (fun i ↦ Nat.cast_nonneg (demand i))
    (by
      intro i
      simp [Pattern.singleton])

@[simp] theorem singletonCover_cost
    (B : BinPackingInstance.{u}) (demand : B.Item → ℕ) :
    (singletonCover B demand).cost = ∑ i : B.Item, (demand i : ℝ) := by
  rw [singletonCover, ofFinitePatterns_cost]

/-- Exact feasibility for a full coefficient vector indexed by the finite
pattern type. -/
def CoefficientFeasible (B : BinPackingInstance.{u})
    (demand : B.Item → ℕ) (x : B.Pattern → ℝ) : Prop :=
  (∀ p, 0 ≤ x p) ∧
    (∀ i, FractionalPatternCover.coefficientCoverage B x i = demand i)

/-- Turn an exact feasible full vector into the finite-support structure. -/
def ofCoefficientFunction (B : BinPackingInstance.{u})
    (demand : B.Item → ℕ) (x : B.Pattern → ℝ)
    (hx : CoefficientFeasible B demand x) :
    B.ExactDemandPatternCover demand := by
  let coeff : B.Pattern →₀ ℝ := Finsupp.equivFunOnFinite.symm x
  refine
    { coeff := coeff
      coeff_nonneg := ?_
      covers_exact := ?_ }
  · intro p
    simpa [coeff] using hx.1 p
  · intro i
    change coeff.sum (fun p c ↦ c * (p.multiplicity i : ℝ)) = demand i
    calc
      coeff.sum (fun p c ↦ c * (p.multiplicity i : ℝ)) =
          ∑ p : B.Pattern, coeff p * (p.multiplicity i : ℝ) := by
            exact Finsupp.sum_fintype coeff
              (fun p c ↦ c * (p.multiplicity i : ℝ)) (by simp)
      _ = FractionalPatternCover.coefficientCoverage B x i := by
        simp [FractionalPatternCover.coefficientCoverage, coeff]
      _ = demand i := hx.2 i

@[simp] theorem ofCoefficientFunction_coeff
    (B : BinPackingInstance.{u}) (demand : B.Item → ℕ)
    (x : B.Pattern → ℝ) (hx : CoefficientFeasible B demand x)
    (p : B.Pattern) :
    (ofCoefficientFunction B demand x hx).coeff p = x p := by
  simp [ofCoefficientFunction]

theorem sum_coeff_eq_cost (C : B.ExactDemandPatternCover demand) :
    (∑ p : B.Pattern, C.coeff p) = C.cost := by
  symm
  exact Finsupp.sum_fintype C.coeff (fun _ c ↦ c) (by simp)

theorem ofCoefficientFunction_cost
    (B : BinPackingInstance.{u}) (demand : B.Item → ℕ)
    (x : B.Pattern → ℝ) (hx : CoefficientFeasible B demand x) :
    (ofCoefficientFunction B demand x hx).cost =
      FractionalPatternCover.coefficientCost B x := by
  rw [← sum_coeff_eq_cost]
  simp [FractionalPatternCover.coefficientCost]

/-- Total prescribed multiplicity, used as a common compact-box bound. -/
def demandTotal (demand : B.Item → ℕ) : ℝ :=
  ∑ i : B.Item, (demand i : ℝ)

theorem demandTotal_nonneg (demand : B.Item → ℕ) :
    0 ≤ demandTotal demand := by
  exact Finset.sum_nonneg fun i _hi ↦ Nat.cast_nonneg (demand i)

/-- Exact feasible vectors inside the box bounded by total demand. -/
def boundedFeasibleSet (B : BinPackingInstance.{u})
    (demand : B.Item → ℕ) : Set (B.Pattern → ℝ) :=
  Set.Icc (fun _ ↦ 0) (fun _ ↦ demandTotal demand) ∩
    {x | ∀ i,
      FractionalPatternCover.coefficientCoverage B x i = demand i}

theorem isClosed_exactCoverageSet
    (B : BinPackingInstance.{u}) (demand : B.Item → ℕ) :
    IsClosed {x : B.Pattern → ℝ | ∀ i,
      FractionalPatternCover.coefficientCoverage B x i = demand i} := by
  rw [show {x : B.Pattern → ℝ | ∀ i,
      FractionalPatternCover.coefficientCoverage B x i = demand i} =
      ⋂ i : B.Item,
        {x | FractionalPatternCover.coefficientCoverage B x i =
          (fun _ : B.Pattern → ℝ ↦ (demand i : ℝ)) x} by
    ext x
    simp]
  apply isClosed_iInter
  intro i
  exact isClosed_eq
    (FractionalPatternCover.continuous_coefficientCoverage B i)
    continuous_const

theorem isCompact_boundedFeasibleSet
    (B : BinPackingInstance.{u}) (demand : B.Item → ℕ) :
    IsCompact (boundedFeasibleSet B demand) := by
  unfold boundedFeasibleSet
  exact isCompact_Icc.inter_right
    (isClosed_exactCoverageSet B demand)

/-- Every exact-demand finite pattern-cover problem has an attained minimum
cost. -/
theorem exists_minimumCost
    (B : BinPackingInstance.{u}) (demand : B.Item → ℕ) :
    ∃ C : B.ExactDemandPatternCover demand, C.IsMinimumCost := by
  let C0 := singletonCover B demand
  let x0 : B.Pattern → ℝ := fun p ↦ C0.coeff p
  have hx0feasible : CoefficientFeasible B demand x0 := by
    constructor
    · intro p
      exact C0.coeff_nonneg p
    · intro i
      calc
        FractionalPatternCover.coefficientCoverage B x0 i =
            C0.coeff.sum
              (fun p c ↦ c * (p.multiplicity i : ℝ)) := by
          exact (Finsupp.sum_fintype C0.coeff
            (fun p c ↦ c * (p.multiplicity i : ℝ)) (by simp)).symm
        _ = C0.coverage i := rfl
        _ = demand i := C0.coverage_eq i
  have hx0cost :
      FractionalPatternCover.coefficientCost B x0 = demandTotal demand := by
    calc
      FractionalPatternCover.coefficientCost B x0 = C0.cost := by
        exact sum_coeff_eq_cost C0
      _ = demandTotal demand := by simp [C0, demandTotal]
  have hx0mem : x0 ∈ boundedFeasibleSet B demand := by
    refine ⟨⟨hx0feasible.1, ?_⟩, hx0feasible.2⟩
    intro p
    calc
      x0 p ≤ ∑ q : B.Pattern, x0 q := by
        exact Finset.single_le_sum
          (fun q _hq ↦ hx0feasible.1 q) (Finset.mem_univ p)
      _ = demandTotal demand := hx0cost
  obtain ⟨x, hx, hxmin⟩ :=
    (isCompact_boundedFeasibleSet B demand).exists_isMinOn
      ⟨x0, hx0mem⟩
      (FractionalPatternCover.continuous_coefficientCost B).continuousOn
  have hxfeasible : CoefficientFeasible B demand x := ⟨hx.1.1, hx.2⟩
  let C := ofCoefficientFunction B demand x hxfeasible
  refine ⟨C, ?_⟩
  intro D
  let y : B.Pattern → ℝ := fun p ↦ D.coeff p
  have hyfeasible : CoefficientFeasible B demand y := by
    constructor
    · intro p
      exact D.coeff_nonneg p
    · intro i
      calc
        FractionalPatternCover.coefficientCoverage B y i =
            D.coeff.sum
              (fun p c ↦ c * (p.multiplicity i : ℝ)) := by
          exact (Finsupp.sum_fintype D.coeff
            (fun p c ↦ c * (p.multiplicity i : ℝ)) (by simp)).symm
        _ = D.coverage i := rfl
        _ = demand i := D.coverage_eq i
  have hycost : FractionalPatternCover.coefficientCost B y = D.cost := by
    exact sum_coeff_eq_cost D
  have hCcost : C.cost =
      FractionalPatternCover.coefficientCost B x := by
    exact ofCoefficientFunction_cost B demand x hxfeasible
  by_cases hDsmall : D.cost ≤ demandTotal demand
  · have hymem : y ∈ boundedFeasibleSet B demand := by
      refine ⟨⟨hyfeasible.1, ?_⟩, hyfeasible.2⟩
      intro p
      calc
        y p ≤ ∑ q : B.Pattern, y q := by
          exact Finset.single_le_sum
            (fun q _hq ↦ hyfeasible.1 q) (Finset.mem_univ p)
        _ = D.cost := hycost
        _ ≤ demandTotal demand := hDsmall
    rw [hCcost]
    calc
      FractionalPatternCover.coefficientCost B x ≤
          FractionalPatternCover.coefficientCost B y := hxmin hymem
      _ = D.cost := hycost
  · have hxsmall :
        FractionalPatternCover.coefficientCost B x ≤ demandTotal demand := by
      calc
        FractionalPatternCover.coefficientCost B x ≤
            FractionalPatternCover.coefficientCost B x0 := hxmin hx0mem
        _ = demandTotal demand := hx0cost
    rw [hCcost]
    exact hxsmall.trans (lt_of_not_ge hDsmall).le

end ExactDemandPatternCover
end
end BinPackingInstance
end WeightedEdgeColoring
