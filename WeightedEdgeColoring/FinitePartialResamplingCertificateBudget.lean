import WeightedEdgeColoring.FinitePartialResamplingWitnessCertificates
import WeightedEdgeColoring.FinitePartialResamplingTreeBudget
import WeightedEdgeColoring.FiniteWitnessCounting

/-!
# Finite budget and counting for canonical witness certificates

A canonical certificate packages its root label with a proper rooted tree at
one fixed depth.  Its weight is the product of the coarse root factors over
all tree nodes.  Summing over the finite sigma type of certificates is
exactly `coarseDepthTreeBudget`.

The last theorem is the finite positive-mass counting step.  Each sample
supplies a history and hence, on positive-mass samples, one distinct
canonical certificate for every endpoint.  The only probabilistic input is
an explicit hypothesis bounding the mass on which each fixed certificate
appears by that certificate's weight.
-/

namespace WeightedEdgeColoring.FinitePartialResamplingCertificateBudget

open scoped BigOperators
open WeightedEdgeColoring.FinitePartialResamplingExponential
open WeightedEdgeColoring.FinitePartialResamplingNeighborPolynomial
open WeightedEdgeColoring.FinitePartialResamplingTreeWeights
open WeightedEdgeColoring.FinitePartialResamplingTreeBudget
open WeightedEdgeColoring.FinitePartialResamplingWitnessCertificates
open WeightedEdgeColoring.FiniteWitnessCounting

variable {Source State Row : Type*}
variable [Fintype Source] [DecidableEq Source]
variable [Fintype State] [DecidableEq State]
variable [Fintype Row] [DecidableEq Row]

/-- Product weight of one fixed-depth canonical certificate. -/
def coarseCertificateWeight
    (q : Row → PartialAssignment Source State → ℝ)
    (p : Source → State → ℝ) {depth : Nat}
    (certificate : CanonicalCertificate Source State Row depth) : ℝ :=
  treeWeight
    (fun a : Label Source State Row ↦
      q a.1 a.2 * partialLambdaProduct p a.2)
    certificate.2

/-- Summing the weights of all dependent root/tree certificates is exactly
the previously defined finite-depth tree budget. -/
theorem sum_coarseCertificateWeight_eq_coarseDepthTreeBudget
    (q : Row → PartialAssignment Source State → ℝ)
    (p : Source → State → ℝ) (depth : Nat) :
    (∑ certificate : CanonicalCertificate Source State Row depth,
      coarseCertificateWeight q p certificate) =
      coarseDepthTreeBudget q p depth := by
  classical
  rw [Fintype.sum_sigma]
  unfold coarseCertificateWeight coarseDepthTreeBudget
  apply Finset.sum_congr rfl
  intro root _hroot
  exact sum_treeWeight_eq_totalProperTreeWeight
    (ProperChildren (Source := Source) (State := State) (Row := Row))
    (fun a : Label Source State Row ↦
      q a.1 a.2 * partialLambdaProduct p a.2)
    depth root

/-- A one-node fallback certificate.  It is used only to make the endpoint
map total on zero-mass samples; the positive-mass counting theorem never
uses its structural properties. -/
noncomputable def emptyCanonicalCertificateTree
    (depth : Nat) (root : Label Source State Row) :
    ProperRootedTree
      (ProperChildren (Source := Source) (State := State) (Row := Row))
      (depth + 1) root := by
  let emptyChildren : {s : Finset (Label Source State Row) //
      ProperChildren root s} := ⟨∅, by simp [ProperChildren]⟩
  refine ⟨emptyChildren, ?_⟩
  intro child
  exact (Finset.notMem_empty child.1 child.2).elim

/-- The true endpoint certificate on a positive-mass sample, and an
irrelevant leaf certificate on a zero-mass sample. -/
noncomputable def positiveMassEndpointCertificate
    {Sample : Type*} {N : Nat}
    (mass : Sample → ℝ)
    (history : Sample → Fin N → Label Source State Row)
    (hnonempty : ∀ sample, 0 < mass sample → ∀ time,
      NonemptyPartial (history sample time).2)
    (sample : Sample) (time : Fin N) :
    CanonicalCertificate Source State Row (N + 1) :=
  if hpos : 0 < mass sample then
    endpointCertificate (history sample) (hnonempty sample hpos) time
  else
    ⟨history sample time,
      emptyCanonicalCertificateTree N (history sample time)⟩

@[simp] theorem positiveMassEndpointCertificate_of_pos
    {Sample : Type*} {N : Nat}
    (mass : Sample → ℝ)
    (history : Sample → Fin N → Label Source State Row)
    (hnonempty : ∀ sample, 0 < mass sample → ∀ time,
      NonemptyPartial (history sample time).2)
    {sample : Sample} (hpos : 0 < mass sample) (time : Fin N) :
    positiveMassEndpointCertificate mass history hnonempty sample time =
      endpointCertificate (history sample) (hnonempty sample hpos) time := by
  simp [positiveMassEndpointCertificate, hpos]

/-- Positive-mass finite witness-counting contradiction for the canonical
endpoint certificates.

`happearance` is the remaining fixed-certificate appearance estimate.  All
other ingredients are finite: normalized nonnegative sample mass, endpoint
certificate injectivity, exact certificate enumeration, and the strict tree
budget. -/
theorem endpointCertificate_counting_contradiction
    {Sample : Type*} [Fintype Sample]
    (N : Nat)
    (mass : Sample → ℝ)
    (history : Sample → Fin N → Label Source State Row)
    (hnonempty : ∀ sample, 0 < mass sample → ∀ time,
      NonemptyPartial (history sample time).2)
    (appears : Sample →
      CanonicalCertificate Source State Row (N + 1) → Prop)
    [DecidableRel appears]
    (q : Row → PartialAssignment Source State → ℝ)
    (p : Source → State → ℝ)
    (hmass_nonneg : ∀ sample, 0 ≤ mass sample)
    (hmass_sum : ∑ sample, mass sample = 1)
    (hcertificate_appears : ∀ sample (hpos : 0 < mass sample) time,
      appears sample
        (endpointCertificate (history sample)
          (hnonempty sample hpos) time))
    (happearance : ∀ certificate,
      (∑ sample,
        if appears sample certificate then mass sample else 0) ≤
      coarseCertificateWeight q p certificate)
    (hbudget : coarseDepthTreeBudget q p (N + 1) < (N : ℝ)) : False := by
  let certificate : Sample → Fin N →
      CanonicalCertificate Source State Row (N + 1) :=
    positiveMassEndpointCertificate mass history hnonempty
  apply not_all_positive_mass_samples_have_N_witnesses_of_sum_lt
    N mass appears (coarseCertificateWeight q p) certificate
  · exact hmass_nonneg
  · exact hmass_sum
  · intro sample hpos
    intro left right heq
    apply endpointCertificate_injective
      (history sample) (hnonempty sample hpos)
    simpa [certificate, positiveMassEndpointCertificate, hpos] using heq
  · intro sample hpos time
    simpa [certificate, positiveMassEndpointCertificate, hpos] using
      hcertificate_appears sample hpos time
  · exact happearance
  · rw [sum_coarseCertificateWeight_eq_coarseDepthTreeBudget]
    exact hbudget

end WeightedEdgeColoring.FinitePartialResamplingCertificateBudget
