import WeightedEdgeColoring.FinitePartialResamplingWitnessCylinder

/-!
# Finite table prefixes prescribed source by source

A canonical witness certificate prescribes, for every source, an initial
list of table states.  This file proves the finite product calculation for
an arbitrary family of such lists.  If every list fits in the chosen finite
table, the required cells are automatically distinct and the mass of all
tables realizing the lists is exactly the product of their one-cell masses.
-/

namespace WeightedEdgeColoring.FinitePartialResamplingTablePrefixes

open scoped BigOperators
open WeightedEdgeColoring.FinitePartialResamplingProcess
open WeightedEdgeColoring.FinitePartialResamplingWitnessCylinder

noncomputable section

variable {Source State : Type*}
variable [Fintype Source] [DecidableEq Source]
variable [Fintype State] [DecidableEq State]

/-- A chronological table prefix for each source. -/
abbrev SourceRequirements (Source State : Type*) := Source → List State

/-- Product of the categorical masses of all prescribed source states.
List products retain repeated states and their multiplicities. -/
def sourceRequirementsWeight
    (prob : Source → State → ℝ)
    (requirements : SourceRequirements Source State) : ℝ :=
  ∏ i, ((requirements i).map (prob i)).prod

theorem sourceRequirementsWeight_nonneg
    {prob : Source → State → ℝ} (hprob : ∀ i a, 0 ≤ prob i a)
    (requirements : SourceRequirements Source State) :
    0 ≤ sourceRequirementsWeight prob requirements := by
  unfold sourceRequirementsWeight
  apply Finset.prod_nonneg
  intro i _hi
  apply List.prod_nonneg
  intro x hx
  rw [List.mem_map] at hx
  obtain ⟨a, _ha, rfl⟩ := hx
  exact hprob i a

/-- Every prescribed source list fits in an `h+1`-cell finite table. -/
def SourceRequirementsFit (h : Nat)
    (requirements : SourceRequirements Source State) : Prop :=
  ∀ i, (requirements i).length ≤ h + 1

/-- One rank-indexed state requirement. -/
abbrev SourceRequirement
    (requirements : SourceRequirements Source State) :=
  Σ i : Source, Fin (requirements i).length

/-- The distinct finite-table cell read by a rank-indexed requirement. -/
def sourceRequirementCell {h : Nat}
    (requirements : SourceRequirements Source State)
    (hfit : SourceRequirementsFit h requirements) :
    SourceRequirement requirements → Source × Fin (h + 1)
  | ⟨i, rank⟩ =>
      (i, ⟨rank.1, lt_of_lt_of_le rank.2 (hfit i)⟩)

/-- State named at one rank of a source prefix. -/
def sourceRequirementState
    (requirements : SourceRequirements Source State) :
    SourceRequirement requirements → State
  | ⟨i, rank⟩ => (requirements i).get rank

theorem sourceRequirementCell_injective {h : Nat}
    (requirements : SourceRequirements Source State)
    (hfit : SourceRequirementsFit h requirements) :
    Function.Injective (sourceRequirementCell requirements hfit) := by
  rintro ⟨leftSource, leftRank⟩ ⟨rightSource, rightRank⟩ hcell
  have hsource : leftSource = rightSource := congrArg Prod.fst hcell
  subst rightSource
  have hrank : leftRank = rightRank := by
    apply Fin.ext
    exact congrArg (fun cell : Source × Fin (h + 1) ↦ cell.2.1) hcell
  subst rightRank
  rfl

/-- A finite table realizes every prescribed source-prefix state. -/
def RealizesSourceRequirements {h : Nat}
    (requirements : SourceRequirements Source State)
    (hfit : SourceRequirementsFit h requirements)
    (T : FiniteResamplingTable Source State h) : Prop :=
  ∀ requirement : SourceRequirement requirements,
    T (sourceRequirementCell requirements hfit requirement).1
        (sourceRequirementCell requirements hfit requirement).2 =
      sourceRequirementState requirements requirement

noncomputable instance realizesSourceRequirementsDecidable {h : Nat}
    (requirements : SourceRequirements Source State)
    (hfit : SourceRequirementsFit h requirements)
    (T : FiniteResamplingTable Source State h) :
    Decidable (RealizesSourceRequirements requirements hfit T) :=
  Classical.propDecidable _

/-- The product over rank-indexed requirements is the list-product weight. -/
theorem prod_sourceRequirement_probability_eq_weight
    (prob : Source → State → ℝ)
    (requirements : SourceRequirements Source State) :
    (∏ requirement : SourceRequirement requirements,
      prob requirement.1
        (sourceRequirementState requirements requirement)) =
      sourceRequirementsWeight prob requirements := by
  classical
  rw [Fintype.prod_sigma]
  unfold sourceRequirementsWeight
  apply Fintype.prod_congr
  intro i
  change
    (∏ rank : Fin (requirements i).length,
      prob i ((requirements i).get rank)) =
        ((requirements i).map (prob i)).prod
  rw [← List.prod_ofFn, List.ofFn_comp', List.ofFn_get]

/-- Exact mass of all finite tables realizing prescribed source prefixes. -/
theorem sum_finiteTableMass_realizing_sourceRequirements {h : Nat}
    (prob : Source → State → ℝ)
    (hprobSum : ∀ i, ∑ a, prob i a = 1)
    (requirements : SourceRequirements Source State)
    (hfit : SourceRequirementsFit h requirements) :
    (∑ T : FiniteResamplingTable Source State h,
      if RealizesSourceRequirements requirements hfit T then
        finiteTableMass prob T
      else 0) = sourceRequirementsWeight prob requirements := by
  classical
  let curryEquiv := Equiv.curry Source (Fin (h + 1)) State
  let cellProb : (Source × Fin (h + 1)) → State → ℝ :=
    fun cell a ↦ prob cell.1 a
  let cell := sourceRequirementCell requirements hfit
  let value := sourceRequirementState requirements
  have hcell : Function.Injective cell :=
    sourceRequirementCell_injective requirements hfit
  have hcellProbSum : ∀ coordinate, ∑ a, cellProb coordinate a = 1 := by
    intro coordinate
    exact hprobSum coordinate.1
  calc
    (∑ T : FiniteResamplingTable Source State h,
        if RealizesSourceRequirements requirements hfit T then
          finiteTableMass prob T
        else 0) =
        ∑ x : (Source × Fin (h + 1)) → State,
          if RealizesCylinder cell value x then
            ∏ coordinate, cellProb coordinate (x coordinate)
          else 0 := by
      apply Fintype.sum_equiv curryEquiv.symm
      intro T
      simp only [curryEquiv, Equiv.curry_symm_apply]
      unfold RealizesSourceRequirements finiteTableMass
      rw [Fintype.prod_prod_type]
      rfl
    _ = ∏ requirement : SourceRequirement requirements,
          cellProb (cell requirement) (value requirement) :=
      sum_cylinderMass_eq_prod cellProb hcellProbSum cell value hcell
    _ = sourceRequirementsWeight prob requirements := by
      simpa [cellProb, cell, value] using
        prod_sourceRequirement_probability_eq_weight prob requirements

end

end WeightedEdgeColoring.FinitePartialResamplingTablePrefixes
