import WeightedEdgeColoring.FinitePartialResamplingTablePrefixes
import WeightedEdgeColoring.FinitePartialResamplingTracePrefixes

/-!
# Mass of simultaneous table and trace prefixes

A fixed canonical witness certificate imposes two independent kinds of
requirements.  Its source lists fix cells of the finite resampling table,
while its row lists fix prefixes of the adaptive patch trace.  This file
combines the exact table-cylinder identity with the adaptive trace-prefix
bound.  The total mass of samples satisfying both families is at most the
product of their two weights.
-/

namespace WeightedEdgeColoring.FinitePartialResamplingPrefixAppearance

open scoped BigOperators
open WeightedEdgeColoring.FinitePartialResamplingExponential
open WeightedEdgeColoring.FinitePartialResamplingProcess
open WeightedEdgeColoring.FinitePartialResamplingFiniteRun
open WeightedEdgeColoring.FinitePartialResamplingTracePrefixes
open WeightedEdgeColoring.FinitePartialResamplingTablePrefixes

noncomputable section

variable {Source State Row : Type*}
variable [Fintype Source] [DecidableEq Source]
variable [Fintype State] [DecidableEq State]
variable [Fintype Row] [DecidableEq Row]

/-- A finite table/trace sample satisfies both a family of source-table
prefixes and a family of adaptive row-patch prefixes. -/
def HasPrefixCertificate
    (rowPolicy : (Source → State) → Row)
    (fallback : Source → State) {n : Nat}
    (sourceRequirements : SourceRequirements Source State)
    (hfit : SourceRequirementsFit n sourceRequirements)
    (rowRequirements : RowRequirements Source State Row)
    (T : FiniteResamplingTable Source State n)
    (trace : PatchTrace Source State n) : Prop :=
  RealizesSourceRequirements sourceRequirements hfit T ∧
    ConsumesRequirements rowPolicy (extendFiniteTable fallback T)
      rowRequirements initialPointer n trace

noncomputable instance hasPrefixCertificateDecidable
    (rowPolicy : (Source → State) → Row)
    (fallback : Source → State) {n : Nat}
    (sourceRequirements : SourceRequirements Source State)
    (hfit : SourceRequirementsFit n sourceRequirements)
    (rowRequirements : RowRequirements Source State Row)
    (T : FiniteResamplingTable Source State n)
    (trace : PatchTrace Source State n) :
    Decidable (HasPrefixCertificate rowPolicy fallback sourceRequirements
      hfit rowRequirements T trace) :=
  Classical.propDecidable _

/-- Fixed-prefix appearance mass factors into the exact source-cylinder
weight and the adaptive row-prefix weight. -/
theorem sum_finiteRunSampleMass_hasPrefixCertificate_le
    (prob : Source → State → ℝ)
    (hprob : ∀ i a, 0 ≤ prob i a)
    (hprobSum : ∀ i, ∑ a, prob i a = 1)
    (weight : Row → PartialAssignment Source State → ℝ)
    (hweight : ∀ r Y, 0 ≤ weight r Y)
    (rowPolicy : (Source → State) → Row)
    (htotal : ∀ z, 1 ≤ compatiblePatchTotal weight (rowPolicy z) z)
    (fallback : Source → State) (n : Nat)
    (sourceRequirements : SourceRequirements Source State)
    (hfit : SourceRequirementsFit n sourceRequirements)
    (rowRequirements : RowRequirements Source State Row) :
    (∑ T : FiniteResamplingTable Source State n,
      ∑ trace : PatchTrace Source State n,
        if HasPrefixCertificate rowPolicy fallback sourceRequirements hfit
            rowRequirements T trace then
          finiteRunSampleMass prob weight rowPolicy fallback T trace
        else 0) ≤
      sourceRequirementsWeight prob sourceRequirements *
        requirementsWeight weight rowRequirements := by
  classical
  have hrowWeight : 0 ≤ requirementsWeight weight rowRequirements :=
    requirementsWeight_nonneg hweight rowRequirements
  have htable : ∀ T : FiniteResamplingTable Source State n,
      (∑ trace : PatchTrace Source State n,
        if HasPrefixCertificate rowPolicy fallback sourceRequirements hfit
            rowRequirements T trace then
          finiteRunSampleMass prob weight rowPolicy fallback T trace
        else 0) ≤
      if RealizesSourceRequirements sourceRequirements hfit T then
        finiteTableMass prob T * requirementsWeight weight rowRequirements
      else 0 := by
    intro T
    by_cases hreal : RealizesSourceRequirements sourceRequirements hfit T
    · have htrace := consumingTraceMass_le_requirementsWeight hweight
          rowPolicy htotal (extendFiniteTable fallback T) n rowRequirements
          initialPointer
      calc
        (∑ trace : PatchTrace Source State n,
            if HasPrefixCertificate rowPolicy fallback sourceRequirements
                hfit rowRequirements T trace then
              finiteRunSampleMass prob weight rowPolicy fallback T trace
            else 0) =
            finiteTableMass prob T *
              consumingTraceMass weight rowPolicy
                (extendFiniteTable fallback T) rowRequirements
                initialPointer n := by
          unfold consumingTraceMass
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro trace _htrace
          simp only [HasPrefixCertificate, hreal, true_and,
            finiteRunSampleMass, finiteTraceMass]
          split <;> ring
        _ ≤ finiteTableMass prob T *
              requirementsWeight weight rowRequirements :=
          mul_le_mul_of_nonneg_left htrace
            (finiteTableMass_nonneg hprob T)
        _ = if RealizesSourceRequirements sourceRequirements hfit T then
              finiteTableMass prob T *
                requirementsWeight weight rowRequirements
            else 0 := by simp [hreal]
    · simp [HasPrefixCertificate, hreal]
  calc
    (∑ T : FiniteResamplingTable Source State n,
        ∑ trace : PatchTrace Source State n,
          if HasPrefixCertificate rowPolicy fallback sourceRequirements hfit
              rowRequirements T trace then
            finiteRunSampleMass prob weight rowPolicy fallback T trace
          else 0) ≤
        ∑ T : FiniteResamplingTable Source State n,
          if RealizesSourceRequirements sourceRequirements hfit T then
            finiteTableMass prob T *
              requirementsWeight weight rowRequirements
          else 0 :=
      Finset.sum_le_sum fun T _hT ↦ htable T
    _ = (∑ T : FiniteResamplingTable Source State n,
          if RealizesSourceRequirements sourceRequirements hfit T then
            finiteTableMass prob T
          else 0) * requirementsWeight weight rowRequirements := by
      rw [Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro T _hT
      split <;> ring
    _ = sourceRequirementsWeight prob sourceRequirements *
          requirementsWeight weight rowRequirements := by
      rw [sum_finiteTableMass_realizing_sourceRequirements
        prob hprobSum sourceRequirements hfit]

end

end WeightedEdgeColoring.FinitePartialResamplingPrefixAppearance
