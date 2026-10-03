import WeightedEdgeColoring.MultigraphColorDependentExtendedProfileLargeQuantizedBridge
import WeightedEdgeColoring.MultigraphDyadicLargeEdgeExtraCaptureBuckets
import WeightedEdgeColoring.MultigraphDyadicLargeEdgeExtraCaptureFiltered
import WeightedEdgeColoring.MultigraphDyadicLargeEdgeTotalLoss
import WeightedEdgeColoring.BoundedMultiplicityLargeEdgeRestriction
import WeightedEdgeColoring.MultigraphProposalTrimTinyRounding
import WeightedEdgeColoring.MultigraphColorDependentExtendedProfileRetainedResidual
import WeightedEdgeColoring.MultigraphDyadicLargeEdgeSelectedSubset

/-!
# Decoding a large-job matching for color-dependent profiles

This is the exact adapter from the existing large-job iteration to the
combined retained-core decoder.  It accounts for both uncovered jobs and
jobs deliberately sent to the private extra-option bank.
-/

namespace WeightedEdgeColoring

open scoped BigOperators

noncomputable section

namespace WeightedMultigraph

universe u v w

variable (G : WeightedMultigraph.{u})
variable {B k n N reserve L : ℕ}
variable {s β q r : ℝ} {hβ : 0 < β} {hr : 0 < r}
variable (proposal : G.E → (Fin B × Fin k) → ℝ)
variable (R : ∀ v c, G.BoundedProfileRealization
  (fun e : G.StarEdge v ↦ proposal e.1 c) s β q r hβ hr)

/-- The small interface needed by the concrete large-matching decoder.  It
packages a matching in the original option system together with the two
facts used by the decoder: all chosen options have large owners, and the
remaining uncovered large load is bounded. -/
structure LargeMatchingDecoderInput
    {Slot : Type v} {Option : Type w}
    [Fintype Slot] [DecidableEq Slot]
    [Fintype Option] [DecidableEq Option]
    (H : RankThreeOptionSystem G.E Slot Option)
    (β traceLoss : ℝ) where
  options : Finset Option
  isPartialMatching : H.IsPartialMatching options
  owner_large : ∀ o ∈ options, β ≤ G.weight (H.owner o)
  uncoveredBound : ∀ x,
    G.uncoveredLargeStarWeight H β options x ≤ traceLoss

/-- Private mass, masked to the large jobs on which the iteration runs. -/
def selectedColorDependentLargeResidual
    (rho omega : ℝ) (selected : G.ColorDependentSelectedStates proposal R)
    (e : G.E) : ℝ :=
  if β ≤ G.weight e then
    G.selectedColorDependentResidualOptionMass proposal R rho omega
      (G.encodedColorDependentSelectedBlock proposal R selected) e
  else 0

theorem selectedColorDependentLargeResidual_nonneg
    (rho omega : ℝ) (selected : G.ColorDependentSelectedStates proposal R) :
    ∀ e, 0 ≤ G.selectedColorDependentLargeResidual
      proposal R rho omega selected e := by
  intro e
  by_cases he : β ≤ G.weight e
  · simp [selectedColorDependentLargeResidual, he,
      G.selectedColorDependentResidualOptionMass_nonneg]
  · simp [selectedColorDependentLargeResidual, he]

theorem selectedColorDependentLargeResidual_le_one
    (hs : 0 ≤ s) (hq : 0 ≤ q) (hr0 : 0 ≤ r)
    (hleft : 0 ≤ 1 - s * (1 + q + r))
    (homega0 : 0 < omega) (homega1 : omega ≤ 1) (hrho : 0 ≤ rho)
    (selected : G.ColorDependentSelectedStates proposal R) :
    ∀ e, G.selectedColorDependentLargeResidual
      proposal R rho omega selected e ≤ 1 := by
  intro e
  by_cases he : β ≤ G.weight e
  · rw [selectedColorDependentLargeResidual, if_pos he]
    unfold selectedColorDependentResidualOptionMass
    exact sub_le_self _ (le_min zero_le_one
      (G.selectedColorDependentAllOptionMass_nonneg proposal R
        hs hq hr0 hleft homega0 homega1 hrho
        (G.encodedColorDependentSelectedBlock proposal R selected) e))
  · simp [selectedColorDependentLargeResidual, he]

theorem sum_flattenedSelectedColorDependentNormalizedLarge_add_residual
    (hs : 0 ≤ s) (hq : 0 ≤ q) (hr0 : 0 ≤ r)
    (hleft : 0 ≤ 1 - s * (1 + q + r))
    (homega0 : 0 < omega) (homega1 : omega ≤ 1) (hrho : 0 ≤ rho)
    (selected : G.ColorDependentSelectedStates proposal R)
    (e : G.E) (he : β ≤ G.weight e) :
    (∑ c : Fin (B * k), ∑ i, ∑ j,
      G.flattenedSelectedColorDependentNormalizedLarge
        proposal R rho omega selected e c i j) +
      G.selectedColorDependentLargeResidual
        proposal R rho omega selected e = 1 := by
  rw [selectedColorDependentLargeResidual, if_pos he]
  have hbase :=
    G.sum_selectedColorDependentNormalizedLarge_add_residual_of_large
      proposal R hs hq hr0 hleft homega0 homega1 hrho
      (G.encodedColorDependentSelectedBlock proposal R selected) e he
  have hreindex :
      (∑ c : Fin (B * k), ∑ i, ∑ j,
        G.flattenedSelectedColorDependentNormalizedLarge
          proposal R rho omega selected e c i j) =
      ∑ c : Fin B × Fin k, ∑ i, ∑ j,
        G.selectedColorDependentNormalizedLargeOptionMass proposal R rho omega
          (G.encodedColorDependentSelectedBlock proposal R selected)
          e c i j := by
    exact Equiv.sum_comp finProdFinEquiv.symm
      (fun c : Fin B × Fin k ↦
        (∑ i, ∑ j,
          G.selectedColorDependentNormalizedLargeOptionMass proposal R rho omega
            (G.encodedColorDependentSelectedBlock proposal R selected)
            e c i j : ℝ))
  simpa [hreindex] using hbase

theorem selectedColorDependentLargeResidual_support
    (rho omega : ℝ) (selected : G.ColorDependentSelectedStates proposal R)
    {e : G.E}
    (he : 0 < G.selectedColorDependentLargeResidual
      proposal R rho omega selected e) :
    β ≤ G.weight e := by
  by_contra hnot
  simp [selectedColorDependentLargeResidual, hnot] at he

/-- The two-part class used by the dyadic large-edge system: the first bit
records whether the edge survives proposal trimming, and the second coordinate
records its dyadic weight bucket. -/
def colorDependentRetainedDyadicBucket
    (proposalGamma β : ℝ) (L : ℕ) (e : G.E) : Bool × Fin (L + 1) :=
  (decide (e ∈ G.retainedMacroscopicEdges proposal proposalGamma β),
    dyadicBucket β L G.weight e)

/-- The concrete quantized local-dyadic option system. -/
def colorDependentSelectedDyadicSystem
    (proposalGamma extraGamma : ℝ) (rho omega : ℝ)
    (selected : G.ColorDependentSelectedStates proposal R) :=
  (G.dyadicLargeEdgeOptionSystem
    (Color := Fin (B * k)) (explicitLargeSlotBound β q r)
    (G.colorDependentRetainedDyadicBucket proposal proposalGamma β L) extraGamma reserve
    (G.selectedColorDependentLargeResidual proposal R rho omega selected)).quantized N
    (G.dyadicLargeEdgeMass (explicitLargeSlotBound β q r)
      (G.colorDependentRetainedDyadicBucket proposal proposalGamma β L) extraGamma reserve
      (G.selectedColorDependentLargeResidual proposal R rho omega selected)
      (G.flattenedSelectedColorDependentNormalizedLarge
        proposal R rho omega selected))

set_option maxHeartbeats 2000000

/-- The ordinary part decoded from a concrete selected dyadic matching.
Keeping this object opaque prevents later decoder statements from repeatedly
expanding the full quantized option system. -/
def colorDependentDecodedOrdinary
    {traceLoss : ℝ}
    (proposalGamma extraGamma rho omega : ℝ)
    (selected : G.ColorDependentSelectedStates proposal R)
    (input : G.LargeMatchingDecoderInput
      (G.colorDependentSelectedDyadicSystem
        (B := B) (k := k) (N := N) (reserve := reserve) (L := L)
        proposal R proposalGamma extraGamma rho omega selected)
      β traceLoss) :
    Finset (OrdinarySlotChoice G.E (Fin (B * k))
      (explicitLargeSlotBound β q r)) :=
  G.selectedDyadicOrdinaryBaseOptions
    (B * k) (explicitLargeSlotBound β q r) N
    (G.colorDependentRetainedDyadicBucket proposal proposalGamma β L)
    extraGamma reserve
    (G.selectedColorDependentLargeResidual proposal R rho omega selected)
    (G.flattenedSelectedColorDependentNormalizedLarge
      proposal R rho omega selected)
    input.options

/-- The named partial-matching proof for the opaque decoded ordinary set. -/
theorem colorDependentDecodedOrdinary_isPartialMatching
    {traceLoss : ℝ}
    (proposalGamma extraGamma rho omega : ℝ)
    (selected : G.ColorDependentSelectedStates proposal R)
    (input : G.LargeMatchingDecoderInput
      (G.colorDependentSelectedDyadicSystem
        (B := B) (k := k) (N := N) (reserve := reserve) (L := L)
        proposal R proposalGamma extraGamma rho omega selected)
      β traceLoss) :
    (OrdinarySlotChoice.system G.fst G.snd
      (explicitLargeSlotBound β q r)).IsPartialMatching
        (G.colorDependentDecodedOrdinary
          (B := B) (k := k) (N := N) (reserve := reserve) (L := L)
          proposal R proposalGamma extraGamma rho omega selected input) := by
  unfold colorDependentDecodedOrdinary
  exact G.selectedDyadicOrdinaryBaseOptions_isPartialMatching
    (B * k) (explicitLargeSlotBound β q r) N
    (G.colorDependentRetainedDyadicBucket proposal proposalGamma β L)
    extraGamma reserve
    (G.selectedColorDependentLargeResidual proposal R rho omega selected)
    (G.flattenedSelectedColorDependentNormalizedLarge
      proposal R rho omega selected)
    input.options input.isPartialMatching

/-- Every edge in the decoded ordinary set is one of the large jobs. -/
theorem colorDependentDecodedOrdinary_subset_largeEdgeJobs
    {traceLoss : ℝ}
    (proposalGamma extraGamma rho omega : ℝ)
    (selected : G.ColorDependentSelectedStates proposal R)
    (input : G.LargeMatchingDecoderInput
      (G.colorDependentSelectedDyadicSystem
        (B := B) (k := k) (N := N) (reserve := reserve) (L := L)
        proposal R proposalGamma extraGamma rho omega selected)
      β traceLoss) :
    G.ordinarySelectedEdges
        (G.colorDependentDecodedOrdinary
          (B := B) (k := k) (N := N) (reserve := reserve) (L := L)
          proposal R proposalGamma extraGamma rho omega selected input) ⊆
      G.largeEdgeJobs β := by
  unfold colorDependentDecodedOrdinary
  apply G.ordinarySelectedEdges_selectedDyadicOrdinaryBaseOptions_subset_largeEdgeJobs
    (G.colorDependentRetainedDyadicBucket proposal proposalGamma β L)
    extraGamma β reserve
    (G.selectedColorDependentLargeResidual proposal R rho omega selected)
    (G.flattenedSelectedColorDependentNormalizedLarge
      proposal R rho omega selected)
    input.options
  intro copy hcopy
  have hlarge := input.owner_large copy hcopy
  change β ≤ G.weight
    ((G.dyadicLargeEdgeOptionSystem
      (Color := Fin (B * k)) (explicitLargeSlotBound β q r)
      (G.colorDependentRetainedDyadicBucket proposal proposalGamma β L)
      extraGamma reserve
      (G.selectedColorDependentLargeResidual proposal R rho omega selected)).owner
        copy.1) at hlarge
  exact hlarge

/-- Positive proposal support for every edge decoded from the ordinary bank. -/
theorem colorDependentDecodedOrdinary_support
    {traceLoss : ℝ}
    (hproposal0 : ∀ e c, 0 ≤ proposal e c)
    (hB : 0 < B) (hk : 0 < k)
    (proposalGamma extraGamma rho omega : ℝ)
    (selected : G.ColorDependentSelectedStates proposal R)
    (input : G.LargeMatchingDecoderInput
      (G.colorDependentSelectedDyadicSystem
        (B := B) (k := k) (N := N) (reserve := reserve) (L := L)
        proposal R proposalGamma extraGamma rho omega selected)
      β traceLoss) :
    let M := G.colorDependentDecodedOrdinary
      (B := B) (k := k) (N := N) (reserve := reserve) (L := L)
      proposal R proposalGamma extraGamma rho omega selected input
    let hM := G.colorDependentDecodedOrdinary_isPartialMatching
      (B := B) (k := k) (N := N) (reserve := reserve) (L := L)
      proposal R proposalGamma extraGamma rho omega selected input
    ∀ e ∈ G.ordinarySelectedEdges M,
      0 < proposal e (finProdFinEquiv.symm
        (G.extendSelectedOrdinaryColor (Nat.mul_pos hB hk) M hM e)) := by
  dsimp only
  exact G.colorDependentSelectedLargeMatching_support proposal R hproposal0
    hB hk rho omega selected
    (G.colorDependentRetainedDyadicBucket proposal proposalGamma β L)
    extraGamma reserve
    (G.selectedColorDependentLargeResidual proposal R rho omega selected)
    input.options input.isPartialMatching

/-- The decoded ordinary load obeys the selected concrete-slot capacities. -/
theorem colorDependentDecodedOrdinary_load_le_concreteSlotSum
    {traceLoss : ℝ}
    (hs : 0 ≤ s) (hq : 0 ≤ q) (hr0 : 0 ≤ r)
    (hleft : 0 ≤ 1 - s * (1 + q + r))
    (homega0 : 0 < omega) (homega1 : omega ≤ 1)
    (rho proposalGamma extraGamma : ℝ)
    (selected : G.ColorDependentSelectedStates proposal R)
    (input : G.LargeMatchingDecoderInput
      (G.colorDependentSelectedDyadicSystem
        (B := B) (k := k) (N := N) (reserve := reserve) (L := L)
        proposal R proposalGamma extraGamma rho omega selected)
      β traceLoss) :
    let M := G.colorDependentDecodedOrdinary
      (B := B) (k := k) (N := N) (reserve := reserve) (L := L)
      proposal R proposalGamma extraGamma rho omega selected input
    let hM := G.colorDependentDecodedOrdinary_isPartialMatching
      (B := B) (k := k) (N := N) (reserve := reserve) (L := L)
      proposal R proposalGamma extraGamma rho omega selected input
    ∀ v c,
      G.selectedOrdinaryIntegralColorLoad M hM v (finProdFinEquiv c) ≤
        ∑ i, G.colorDependentExtendedProfileConcreteSlotSize R v c
          (selected v c.1 c.2) i := by
  dsimp only
  exact G.colorDependentSelectedLargeMatching_load_le_concreteSlotSum
    proposal R hs hq hr0 hleft homega0 homega1 rho selected
    (G.colorDependentRetainedDyadicBucket proposal proposalGamma β L)
    extraGamma reserve
    (G.selectedColorDependentLargeResidual proposal R rho omega selected)
    input.options input.isPartialMatching

/-- The uncovered retained macroscopic load of the opaque decoded set. -/
theorem colorDependentDecodedOrdinary_loss
    {traceLoss : ℝ}
    (proposalGamma extraGamma rho omega : ℝ)
    (selected : G.ColorDependentSelectedStates proposal R)
    (hdyadicCover : 1 ≤ dyadicScale β L)
    (hdyadicTop : dyadicScale β L ≤ 2)
    (hreserve : 0 < reserve) (hextraGamma1 : extraGamma < 1)
    (input : G.LargeMatchingDecoderInput
      (G.colorDependentSelectedDyadicSystem
        (B := B) (k := k) (N := N) (reserve := reserve) (L := L)
        proposal R proposalGamma extraGamma rho omega selected)
      β traceLoss) :
    ∀ v,
      (∑ e ∈ G.retainedMacroscopicEdges proposal proposalGamma β \
          G.ordinarySelectedEdges
            (G.colorDependentDecodedOrdinary
              (B := B) (k := k) (N := N) (reserve := reserve) (L := L)
              proposal R proposalGamma extraGamma rho omega selected input),
        if G.Inc v e then G.weight e else 0) ≤
      traceLoss +
        4 * G.weightedResidualStar
          (G.selectedColorDependentRetainedMacroscopicResidual
            proposal R proposalGamma β rho omega
            (G.encodedColorDependentSelectedBlock proposal R selected)) v /
            (1 - extraGamma) +
        8 * (1 + (reserve : ℝ)) := by
  intro v
  let Q := input.options
  have hQ :
      (G.colorDependentSelectedDyadicSystem
        (B := B) (k := k) (N := N) (reserve := reserve) (L := L)
        proposal R proposalGamma extraGamma rho omega selected).IsPartialMatching Q :=
    input.isPartialMatching
  let residual := G.selectedColorDependentLargeResidual
    proposal R rho omega selected
  let x := G.flattenedSelectedColorDependentNormalizedLarge
    proposal R rho omega selected
  let bucket : G.E → Bool × Fin (L + 1) := G.colorDependentRetainedDyadicBucket proposal proposalGamma β L
  have hlarge :=
    G.retainedDyadicRemainingStarWeight_le_uncovered_add_trueExtra
      (explicitLargeSlotBound β q r) N β bucket extraGamma reserve
      residual x Q hQ
      (G.retainedMacroscopicEdges proposal proposalGamma β)
      (fun e he ↦ G.mem_largeEdgeJobs.mpr
        ((Finset.mem_filter.mp he).2.2))
      (fun e he ↦ by
        simp [bucket, colorDependentRetainedDyadicBucket, he]) v
  have hextra := G.selectedDyadicExtraEdges_trueBank_le_weightedResidual
    (explicitLargeSlotBound β q r) N bucket extraGamma 2 reserve
    residual x Q hQ
    (G.selectedColorDependentLargeResidual_nonneg proposal R rho omega selected)
    hreserve hextraGamma1 (dyadicUpper β)
    (fun h ↦ dyadicUpper_nonneg hβ.le h)
    (fun e ↦ weight_le_dyadicUpper_bucket β L G.weight hdyadicCover
      (fun f _ ↦ G.weight_le_one f) (Finset.mem_univ e))
    (fun e hflag _he ↦ by
      have heret : e ∈ G.retainedMacroscopicEdges proposal proposalGamma β := by
        simpa [bucket, colorDependentRetainedDyadicBucket] using hflag
      exact dyadicUpper_bucket_le_two_mul β L G.weight hβ
        hdyadicCover
        (fun f hf ↦ by
          have hfe : f = e := Finset.mem_singleton.mp hf
          subst f
          exact (Finset.mem_filter.mp heret).2.2)
        (fun f _ ↦ G.weight_le_one f)
        (by simp : e ∈ ({e} : Finset G.E))) v
  have hsum := sum_dyadicUpper_le_two_mul_top hβ.le L
  have hsum4 : (∑ h : Fin (L + 1), dyadicUpper β h) ≤ 4 :=
    hsum.trans (by nlinarith [hdyadicTop])
  have hmask : G.boolBucketResidual bucket residual =
      G.selectedColorDependentRetainedMacroscopicResidual
        proposal R proposalGamma β rho omega
        (G.encodedColorDependentSelectedBlock proposal R selected) := by
    funext e
    by_cases he : e ∈ G.retainedMacroscopicEdges proposal proposalGamma β
    · have helarge : β ≤ G.weight e := (Finset.mem_filter.mp he).2.2
      simp [WeightedMultigraph.boolBucketResidual, bucket,
        colorDependentRetainedDyadicBucket, residual,
        selectedColorDependentLargeResidual, he, helarge,
        selectedColorDependentRetainedMacroscopicResidual]
    · simp [WeightedMultigraph.boolBucketResidual, bucket,
        colorDependentRetainedDyadicBucket, residual,
        selectedColorDependentRetainedMacroscopicResidual, he]
  rw [hmask] at hextra
  have hextra' :
      (∑ e ∈ (G.selectedDyadicExtraEdges
        (explicitLargeSlotBound β q r) N bucket extraGamma reserve
        residual x Q).filter
          (fun e ↦ G.Inc v e ∧ (bucket e).1 = true), G.weight e) ≤
        4 * G.weightedResidualStar
          (G.selectedColorDependentRetainedMacroscopicResidual
            proposal R proposalGamma β rho omega
            (G.encodedColorDependentSelectedBlock proposal R selected)) v /
            (1 - extraGamma) + 8 * (1 + (reserve : ℝ)) := by
    have hreserveBound :
        2 * (1 + (reserve : ℝ)) *
            (∑ h : Fin (L + 1), dyadicUpper β h) ≤
          8 * (1 + (reserve : ℝ)) := by
      have hnonneg : 0 ≤ 2 * (1 + (reserve : ℝ)) := by positivity
      have hbound := mul_le_mul_of_nonneg_left hsum4 hnonneg
      nlinarith
    nlinarith [hextra, hreserveBound]
  have hlarge' := hlarge.trans
    (add_le_add (input.uncoveredBound v) hextra')
  change
    (∑ e ∈ G.retainedMacroscopicEdges proposal proposalGamma β \
        G.selectedDyadicOrdinaryEdges
          (explicitLargeSlotBound β q r) N bucket extraGamma reserve
            residual x Q,
      if G.Inc v e then G.weight e else 0) ≤
      traceLoss +
        4 * G.weightedResidualStar
          (G.selectedColorDependentRetainedMacroscopicResidual
            proposal R proposalGamma β rho omega
            (G.encodedColorDependentSelectedBlock proposal R selected)) v /
            (1 - extraGamma) +
        8 * (1 + (reserve : ℝ))
  simpa only [add_assoc] using hlarge'

/-- Decode a completed matching on all `β`-large jobs.  The resulting
ordinary matching supplies all structural hypotheses of the retained-core
decoder.  Its loss includes uncovered jobs and the selected private-extra
mass, with the latter paid by the usual dyadic capture bound. -/
theorem exists_colorDependentLargeMatchingData_of_restrictedMatching
    (hs : 0 ≤ s) (hq : 0 ≤ q) (hr0 : 0 ≤ r)
    (hleft : 0 ≤ 1 - s * (1 + q + r))
    (homega0 : 0 < omega) (homega1 : omega ≤ 1)
    (rho proposalGamma extraGamma traceLoss : ℝ) (hrho : 0 ≤ rho)
    (hproposal0 : ∀ e c, 0 ≤ proposal e c)
    (hB : 0 < B) (hk : 0 < k)
    (selected : G.ColorDependentSelectedStates proposal R)
    (hdyadicCover : 1 ≤ dyadicScale β L)
    (hdyadicTop : dyadicScale β L ≤ 2)
    (hreserve : 0 < reserve) (hextraGamma1 : extraGamma < 1) :
    let Hbase := G.colorDependentSelectedDyadicSystem
      (B := B) (k := k) (N := N) (reserve := reserve) (L := L)
      proposal R proposalGamma extraGamma rho omega selected
    ∀ input : G.LargeMatchingDecoderInput Hbase β traceLoss,
    ∃ (M : Finset (OrdinarySlotChoice G.E (Fin (B * k))
          (explicitLargeSlotBound β q r)))
      (hM : (OrdinarySlotChoice.system G.fst G.snd
          (explicitLargeSlotBound β q r)).IsPartialMatching M),
      G.ordinarySelectedEdges M ⊆ G.largeEdgeJobs β ∧
      (∀ e ∈ G.ordinarySelectedEdges M,
        0 < proposal e (finProdFinEquiv.symm
          (G.extendSelectedOrdinaryColor (Nat.mul_pos hB hk) M hM e))) ∧
      (∀ v c,
        G.selectedOrdinaryIntegralColorLoad M hM v (finProdFinEquiv c) ≤
          ∑ i, G.colorDependentExtendedProfileConcreteSlotSize R v c
            (selected v c.1 c.2) i) ∧
      ∀ v,
        (∑ e ∈ G.retainedMacroscopicEdges proposal proposalGamma β \
            G.ordinarySelectedEdges M,
          if G.Inc v e then G.weight e else 0) ≤
        traceLoss +
          4 * G.weightedResidualStar
            (G.selectedColorDependentRetainedMacroscopicResidual
              proposal R proposalGamma β rho omega
              (G.encodedColorDependentSelectedBlock proposal R selected)) v /
              (1 - extraGamma) +
          8 * (1 + (reserve : ℝ)) := by
  dsimp only
  intro input
  let M := G.colorDependentDecodedOrdinary
    (B := B) (k := k) (N := N) (reserve := reserve) (L := L)
    proposal R proposalGamma extraGamma rho omega selected input
  let hM := G.colorDependentDecodedOrdinary_isPartialMatching
    (B := B) (k := k) (N := N) (reserve := reserve) (L := L)
    proposal R proposalGamma extraGamma rho omega selected input
  have hsubset := G.colorDependentDecodedOrdinary_subset_largeEdgeJobs
    (B := B) (k := k) (N := N) (reserve := reserve) (L := L)
    proposal R proposalGamma extraGamma rho omega selected input
  have hsupport := G.colorDependentDecodedOrdinary_support
    (B := B) (k := k) (N := N) (reserve := reserve) (L := L)
    proposal R hproposal0 hB hk proposalGamma extraGamma rho omega
    selected input
  have hload := G.colorDependentDecodedOrdinary_load_le_concreteSlotSum
    (B := B) (k := k) (N := N) (reserve := reserve) (L := L)
    proposal R hs hq hr0 hleft homega0 homega1 rho proposalGamma
    extraGamma selected input
  have hloss := G.colorDependentDecodedOrdinary_loss
    (B := B) (k := k) (N := N) (reserve := reserve) (L := L)
    proposal R proposalGamma extraGamma rho omega selected
    hdyadicCover hdyadicTop hreserve hextraGamma1 input
  exact ⟨M, hM, hsubset, hsupport, hload, hloss⟩

end WeightedMultigraph

end

end WeightedEdgeColoring
