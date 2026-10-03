import WeightedEdgeColoring.FinitePartialResamplingBadRows
import WeightedEdgeColoring.FinitePartialResamplingNonemptyTrace
import WeightedEdgeColoring.FinitePartialResamplingWitnessPrefixes
import WeightedEdgeColoring.FinitePartialResamplingCertificateRequirements
import WeightedEdgeColoring.FinitePartialResamplingCertificatePrefixes

/-!
# The finite coarse partial-resampling criterion

This file closes the finite partial-resampling argument.  If every complete
state had a bad row, the deterministic bad-row policy would generate a
normalized table/trace run of any finite length.  A positive-mass sample
gives a nonempty realized history.  Every endpoint of that history has a
canonical certificate, whose source and row prefixes occur in the sample.
The fixed-certificate prefix estimate and finite witness counting then
contradict the coarse tree budget at its natural strict horizon.

No probability space or infinitary termination argument is used.
-/

namespace WeightedEdgeColoring.FinitePartialResamplingCriterion

open scoped BigOperators
open WeightedEdgeColoring.FinitePartialResamplingExponential
open WeightedEdgeColoring.FinitePartialResamplingNeighborPolynomial
open WeightedEdgeColoring.FinitePartialResamplingProcess
open WeightedEdgeColoring.FinitePartialResamplingFiniteRun
open WeightedEdgeColoring.FinitePartialResamplingBadRows
open WeightedEdgeColoring.FinitePartialResamplingNonemptyTrace
open WeightedEdgeColoring.FinitePartialResamplingTracePrefixes
open WeightedEdgeColoring.FinitePartialResamplingTablePrefixes
open WeightedEdgeColoring.FinitePartialResamplingWitnessStructure
open WeightedEdgeColoring.FinitePartialResamplingWitnessCertificates
open WeightedEdgeColoring.FinitePartialResamplingWitnessPrefixes
open WeightedEdgeColoring.FinitePartialResamplingCertificateRequirements
open WeightedEdgeColoring.FinitePartialResamplingCertificatePrefixes
open WeightedEdgeColoring.FinitePartialResamplingTreeBudget

noncomputable section

variable {Source State Row : Type*}
variable [Fintype Source] [DecidableEq Source]
variable [Fintype State] [DecidableEq State]
variable [Fintype Row] [DecidableEq Row]

/-- A normalized finite categorical law supplies a fallback state at every
source.  This is used only beyond the finite table prefix. -/
private theorem exists_nonzero_state
    (p : Source → State → ℝ)
    (hprobSum : ∀ i, ∑ a, p i a = 1) (i : Source) :
    ∃ a : State, p i a ≠ 0 := by
  by_contra hnone
  push_neg at hnone
  have hzero : (∑ a, p i a) = 0 := by
    apply Finset.sum_eq_zero
    intro a _ha
    exact hnone a
  rw [hprobSum i] at hzero
  norm_num at hzero

/-- Coarse finite partial-resampling criterion. -/
theorem exists_completeState_avoiding_badRows
    (p lambda : Source → State → ℝ)
    (hprob : ∀ i a, 0 ≤ p i a)
    (hprobSum : ∀ i, ∑ a, p i a = 1)
    (hlambda : ∀ i a, 0 ≤ lambda i a)
    (hscale : ∀ i a, lambda i a = lambdaTotal lambda i * p i a)
    (q : Row → PartialAssignment Source State → ℝ)
    (hq : ∀ r Y, 0 ≤ q r Y)
    (hempty : ∀ r, q r emptyPartial = 0)
    (bad : Row → (Source → State) → Prop)
    (hhit : ∀ r z, bad r z → 1 ≤ compatiblePatchTotal q r z)
    (hself : ∀ r, coarseSelfCharge q lambda r < 1)
    (hsource : ∀ i,
      (∑ r, coarseSourceCharge q lambda r i /
        (1 - coarseSelfCharge q lambda r)) ≤ lambdaTotal lambda i - 1) :
    ∃ z : Source → State, ∀ r, ¬ bad r z := by
  classical
  by_contra havoid
  have hall : ∀ z : Source → State, ∃ r, bad r z := by
    intro z
    by_contra hrow
    apply havoid
    refine ⟨z, ?_⟩
    intro r hbad
    exact hrow ⟨r, hbad⟩
  let rowPolicy : (Source → State) → Row := badRowPolicy bad hall
  have htotal : ∀ z,
      1 ≤ compatiblePatchTotal q (rowPolicy z) z := by
    intro z
    exact badRowPolicy_compatiblePatchTotal_ge_one bad hall q hhit z
  let fallback : Source → State :=
    fun i ↦ Classical.choose (exists_nonzero_state p hprobSum i)
  let N : Nat := coarseWitnessHorizon q lambda
  have hbudget : coarseDepthTreeBudget q p (N + 1) < (N : ℝ) := by
    simpa [N] using
      (coarseDepthTreeBudget_lt_horizon_and_pos hq hprob hlambda
        hscale hself hsource (coarseWitnessHorizon q lambda + 1)).1
  let sourceRequirements :
      CanonicalCertificate Source State Row (N + 1) →
        SourceRequirements Source State :=
    certificateSourceStateRequirements
  let rowRequirements :
      CanonicalCertificate Source State Row (N + 1) →
        RowRequirements Source State Row :=
    certificateRowRequirements
  let history : FiniteRunSample Source State N →
      Fin N → Label Source State Row :=
    fun sample ↦
      traceHistoryFunction rowPolicy
        (extendFiniteTable fallback sample.1) initialPointer N sample.2
  have hhistoryNonempty : ∀ sample : FiniteRunSample Source State N,
      0 < finiteRunPairMass p q rowPolicy fallback sample →
        ∀ time, NonemptyPartial (history sample time).2 := by
    intro sample hpos
    have htrace0 :
        0 ≤ finiteTraceMass q rowPolicy fallback sample.1 sample.2 :=
      finiteTraceMass_nonneg hq rowPolicy htotal fallback sample.1 sample.2
    have htracePos :
        0 < finiteTraceMass q rowPolicy fallback sample.1 sample.2 := by
      by_contra hnot
      have hzero :
          finiteTraceMass q rowPolicy fallback sample.1 sample.2 = 0 :=
        le_antisymm (le_of_not_gt hnot) htrace0
      rw [finiteRunPairMass, finiteRunSampleMass, hzero, mul_zero] at hpos
      exact (lt_irrefl 0 hpos)
    have htraceNonempty : ∀ time, NonemptyPartial (sample.2 time) :=
      finiteTrace_nonempty_of_mass_pos hq hempty rowPolicy htotal fallback
        sample.1 sample.2 htracePos
    simpa [history] using
      traceHistoryFunction_nonempty rowPolicy
        (extendFiniteTable fallback sample.1) initialPointer N sample.2
        htraceNonempty
  apply endpointCertificate_counting_contradiction_of_prefixes
    N p hprob hprobSum q hq rowPolicy htotal fallback
    sourceRequirements rowRequirements history hhistoryNonempty
  · intro sample hpos endpoint
    let historySample := history sample
    let hnonemptySample : ∀ time,
        NonemptyPartial (historySample time).2 :=
      hhistoryNonempty sample hpos
    let certificate : CanonicalCertificate Source State Row (N + 1) :=
      endpointCertificate historySample hnonemptySample endpoint
    have hfit : SourceRequirementsFit N
        (sourceRequirements certificate) := by
      simpa [sourceRequirements, certificate, historySample] using
        certificateSourceStateRequirements_endpoint_fit
          historySample hnonemptySample endpoint
    rw [PrefixCertificateAppears, dif_pos hfit]
    constructor
    · have htracePos :
          0 < finiteTraceMass q rowPolicy fallback sample.1 sample.2 := by
        have htrace0 :
            0 ≤ finiteTraceMass q rowPolicy fallback sample.1 sample.2 :=
          finiteTraceMass_nonneg hq rowPolicy htotal fallback
            sample.1 sample.2
        by_contra hnot
        have hzero :
            finiteTraceMass q rowPolicy fallback sample.1 sample.2 = 0 :=
          le_antisymm (le_of_not_gt hnot) htrace0
        rw [finiteRunPairMass, finiteRunSampleMass, hzero, mul_zero] at hpos
        exact (lt_irrefl 0 hpos)
      have hrealized :=
        (finiteBadTraceHistory_legal_of_mass_pos bad hall hq hhit fallback
          sample.1 sample.2 htracePos).1
      have hhistoryRealized :
          Realizes (extendFiniteTable fallback sample.1)
            (List.ofFn historySample) := by
        rw [show List.ofFn historySample =
            finiteTraceHistory rowPolicy fallback sample.1 sample.2 by
          simpa [historySample, history, rowPolicy, finiteTraceHistory] using
            ofFn_traceHistoryFunction rowPolicy
              (extendFiniteTable fallback sample.1) initialPointer N sample.2]
        exact hrealized
      have hcard :
          (witnessAt historySample endpoint).nodes.card < N + 1 :=
        witnessAt_nodes_card_lt_horizon_succ historySample endpoint
      have hwitness := realizesWitnessTable_of_realizes_history
        historySample endpoint hcard fallback sample.1 hhistoryRealized
      exact realizes_certificateSourceStateRequirements_endpoint
        historySample hnonemptySample endpoint hfit hcard sample.1 hwitness
    · have hconsumes :=
        trace_consumes_endpoint_witness_requirements rowPolicy
          (extendFiniteTable fallback sample.1) initialPointer N sample.2
          endpoint
      simpa [rowRequirements, certificate, historySample, history,
        certificateRowRequirements_endpointCertificate] using hconsumes
  · intro certificate
    simpa [sourceRequirements, rowRequirements] using
      certificateRequirementsWeight_eq_coarseCertificateWeight
        q p certificate
  · exact hbudget

end

end WeightedEdgeColoring.FinitePartialResamplingCriterion
