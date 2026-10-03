import WeightedEdgeColoring.FinitePartialResamplingPrefixAppearance
import WeightedEdgeColoring.FinitePartialResamplingCertificateBudget

/-!
# Witness counting from canonical prefix requirements

This file packages the final finite double-counting step independently of
the concrete encoding of canonical certificates.  Each certificate is
assigned source-table prefixes and adaptive row-patch prefixes.  If endpoint
certificates really impose those prefixes and the product of their prefix
weights is the canonical tree weight, then a tree budget below the horizon
contradicts the existence of an `N`-step run of total mass one.
-/

namespace WeightedEdgeColoring.FinitePartialResamplingCertificatePrefixes

open scoped BigOperators
open WeightedEdgeColoring.FinitePartialResamplingExponential
open WeightedEdgeColoring.FinitePartialResamplingProcess
open WeightedEdgeColoring.FinitePartialResamplingFiniteRun
open WeightedEdgeColoring.FinitePartialResamplingNeighborPolynomial
open WeightedEdgeColoring.FinitePartialResamplingTracePrefixes
open WeightedEdgeColoring.FinitePartialResamplingTablePrefixes
open WeightedEdgeColoring.FinitePartialResamplingPrefixAppearance
open WeightedEdgeColoring.FinitePartialResamplingWitnessCertificates
open WeightedEdgeColoring.FinitePartialResamplingCertificateBudget
open WeightedEdgeColoring.FinitePartialResamplingTreeBudget

noncomputable section

variable {Source State Row : Type*}
variable [Fintype Source] [DecidableEq Source]
variable [Fintype State] [DecidableEq State]
variable [Fintype Row] [DecidableEq Row]

/-- Product sample space used by a finite table/trace run. -/
abbrev FiniteRunSample (Source State : Type*) [Fintype Source]
    [Fintype State] (n : Nat) :=
  FiniteResamplingTable Source State n × PatchTrace Source State n

/-- Product mass on the finite table/trace sample space. -/
def finiteRunPairMass
    (prob : Source → State → ℝ)
    (weight : Row → PartialAssignment Source State → ℝ)
    (rowPolicy : (Source → State) → Row)
    (fallback : Source → State) {n : Nat}
    (sample : FiniteRunSample Source State n) : ℝ :=
  finiteRunSampleMass prob weight rowPolicy fallback sample.1 sample.2

/-- Appearance event defined by the deterministic source and row prefixes
assigned to a canonical certificate. -/
def PrefixCertificateAppears
    (rowPolicy : (Source → State) → Row)
    (fallback : Source → State) {n : Nat}
    (sourceRequirements :
      CanonicalCertificate Source State Row (n + 1) →
        SourceRequirements Source State)
    (rowRequirements :
      CanonicalCertificate Source State Row (n + 1) →
        RowRequirements Source State Row)
    (sample : FiniteRunSample Source State n)
    (certificate : CanonicalCertificate Source State Row (n + 1)) : Prop := by
  classical
  exact
    if hfit : SourceRequirementsFit n (sourceRequirements certificate) then
      HasPrefixCertificate rowPolicy fallback
        (sourceRequirements certificate) hfit
        (rowRequirements certificate) sample.1 sample.2
    else False

noncomputable instance prefixCertificateAppearsDecidableRel
    (rowPolicy : (Source → State) → Row)
    (fallback : Source → State) {n : Nat}
    (sourceRequirements :
      CanonicalCertificate Source State Row (n + 1) →
        SourceRequirements Source State)
    (rowRequirements :
      CanonicalCertificate Source State Row (n + 1) →
        RowRequirements Source State Row) :
    DecidableRel (PrefixCertificateAppears rowPolicy fallback
      sourceRequirements rowRequirements) :=
  fun _sample _certificate ↦ Classical.propDecidable _

/-- Abstract canonical-prefix form of the finite witness contradiction. -/
theorem endpointCertificate_counting_contradiction_of_prefixes
    (N : Nat)
    (prob : Source → State → ℝ)
    (hprob : ∀ i a, 0 ≤ prob i a)
    (hprobSum : ∀ i, ∑ a, prob i a = 1)
    (weight : Row → PartialAssignment Source State → ℝ)
    (hweight : ∀ r Y, 0 ≤ weight r Y)
    (rowPolicy : (Source → State) → Row)
    (htotal : ∀ z, 1 ≤ compatiblePatchTotal weight (rowPolicy z) z)
    (fallback : Source → State)
    (sourceRequirements :
      CanonicalCertificate Source State Row (N + 1) →
        SourceRequirements Source State)
    (rowRequirements :
      CanonicalCertificate Source State Row (N + 1) →
        RowRequirements Source State Row)
    (history : FiniteRunSample Source State N →
      Fin N → Label Source State Row)
    (hnonempty : ∀ sample,
      0 < finiteRunPairMass prob weight rowPolicy fallback sample →
        ∀ time, NonemptyPartial (history sample time).2)
    (hendpoint : ∀ sample
      (hpos : 0 < finiteRunPairMass prob weight rowPolicy fallback sample)
      (time : Fin N),
      PrefixCertificateAppears rowPolicy fallback sourceRequirements
        rowRequirements sample
        (endpointCertificate (history sample)
          (hnonempty sample hpos) time))
    (hweight_eq : ∀ certificate,
      sourceRequirementsWeight prob (sourceRequirements certificate) *
          requirementsWeight weight (rowRequirements certificate) =
        coarseCertificateWeight weight prob certificate)
    (hbudget : coarseDepthTreeBudget weight prob (N + 1) < (N : ℝ)) :
    False := by
  let mass : FiniteRunSample Source State N → ℝ :=
    finiteRunPairMass prob weight rowPolicy fallback
  let appears : FiniteRunSample Source State N →
      CanonicalCertificate Source State Row (N + 1) → Prop :=
    PrefixCertificateAppears rowPolicy fallback sourceRequirements
      rowRequirements
  apply endpointCertificate_counting_contradiction N mass history hnonempty
    appears weight prob
  · intro sample
    exact finiteRunSampleMass_nonneg hprob hweight rowPolicy htotal fallback
      sample.1 sample.2
  · change
      (∑ sample : FiniteResamplingTable Source State N ×
          PatchTrace Source State N,
        finiteRunSampleMass prob weight rowPolicy fallback
          sample.1 sample.2) = 1
    rw [Fintype.sum_prod_type]
    exact sum_finiteRunSampleMass prob hprobSum weight rowPolicy htotal
      fallback N
  · exact hendpoint
  · intro certificate
    by_cases hfitCert :
        SourceRequirementsFit N (sourceRequirements certificate)
    · change
        (∑ sample : FiniteResamplingTable Source State N ×
            PatchTrace Source State N,
          if PrefixCertificateAppears rowPolicy fallback sourceRequirements
              rowRequirements sample certificate then
            finiteRunSampleMass prob weight rowPolicy fallback
              sample.1 sample.2
          else 0) ≤ coarseCertificateWeight weight prob certificate
      rw [Fintype.sum_prod_type]
      have hprefix :=
        sum_finiteRunSampleMass_hasPrefixCertificate_le prob hprob
          hprobSum weight hweight rowPolicy htotal fallback N
          (sourceRequirements certificate) hfitCert
          (rowRequirements certificate)
      have hprefix' :
          (∑ T : FiniteResamplingTable Source State N,
            ∑ trace : PatchTrace Source State N,
              if PrefixCertificateAppears rowPolicy fallback
                  sourceRequirements rowRequirements (T, trace)
                  certificate then
                finiteRunSampleMass prob weight rowPolicy fallback T trace
              else 0) ≤
            sourceRequirementsWeight prob (sourceRequirements certificate) *
              requirementsWeight weight (rowRequirements certificate) := by
        simpa [PrefixCertificateAppears, hfitCert] using hprefix
      exact hprefix'.trans_eq (hweight_eq certificate)
    · have hcertificate_nonneg :
          0 ≤ coarseCertificateWeight weight prob certificate := by
        rw [← hweight_eq certificate]
        exact mul_nonneg
          (sourceRequirementsWeight_nonneg hprob
            (sourceRequirements certificate))
          (requirementsWeight_nonneg hweight
            (rowRequirements certificate))
      simpa [appears, PrefixCertificateAppears, hfitCert] using
        hcertificate_nonneg
  · exact hbudget

end

end WeightedEdgeColoring.FinitePartialResamplingCertificatePrefixes
