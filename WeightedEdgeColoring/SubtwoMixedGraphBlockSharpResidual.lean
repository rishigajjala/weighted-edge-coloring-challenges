import WeightedEdgeColoring.SubtwoMixedGraphBlockVarianceSelected

/-! The actual joint mixed selector retains its sharp product-law variance mean. -/

namespace WeightedEdgeColoring

open scoped BigOperators

noncomputable section

namespace WeightedMultigraph

variable (G : WeightedMultigraph)
variable {B k : ℕ} {Label : Type*} [Fintype Label] [DecidableEq Label]
variable (proposal : G.E → (Fin B × Fin k) → ℝ)
variable (edgeLabel : ∀ v : G.V, G.StarEdge v → Label)
variable (qLaw : ∀ v : G.V, (Fin B × Fin k) →
  Finset (G.StarEdge v) → ℝ)
variable {s β qstep r : ℝ} {hβ : 0 < β} {hr : 0 < r}
variable (R : ∀ v c label,
  G.BoundedProfileRealization
    (G.conditionalEndpointProposal (edgeLabel v)
      (fun e : G.StarEdge v ↦ proposal e.1 c) (qLaw v c) label)
    s β qstep r hβ hr)

/-- A supported joint choice has the sharp selected-variance and clipped
residual bounds.  The deviation is the one delivered by the actual joint
categorical selector; the theorem does not involve the number of vertices. -/
theorem exists_mixedGraphSupportedBlockChoice_sharpResidual
    {L n : ℕ} (hL : 0 < L) (hmult : G.PairMultiplicityAtMost L)
    (hn : 0 < n) (hk : 0 < k)
    (hq0 : ∀ v c S, 0 ≤ qLaw v c S)
    (hqmarg : ∀ v c (f : G.StarEdge v),
      (∑ S, if f ∈ S then qLaw v c S else 0) = proposal f.1 c)
    (hqsingle : ∀ v c S, qLaw v c S ≠ 0 → S ≠ ∅ →
      ∃ label : Label, ∀ f ∈ S, edgeLabel v f = label)
    (hqsum : ∀ v c, ∑ S, qLaw v c S = 1)
    (hs : 0 < s) (hqstep : 0 ≤ qstep) (hr0 : 0 ≤ r)
    (hleft : 0 ≤ 1 - s * (1 + qstep + r))
    (homega0 : 0 < omega) (homega1 : omega < 1)
    (hrho : 0 < rho) (hC0 : 0 < C0)
    (hproposal0 : ∀ e c, 0 ≤ proposal e c)
    (hproposal : ∀ e c, proposal e c ≤ C0 / (n : ℝ))
    (hmass : ∀ e, ∑ c : Fin B × Fin k, proposal e c ≤ 1)
    (hstar : ∀ v, G.starWeight v ≤ n)
    (t : ℝ) (ht : 0 < t) :
    let candidateScale := (L : ℝ) *
      mixedCandidateOrientedScale (Label := Label)
        (β := β) (qstep := qstep) (r := r) rho s omega C0
    let unitScale := mixedBlockVarianceUnitScale (k := k) (s := s)
      (Label := Label) (β := β) (qstep := qstep) (r := r)
      n rho omega C0
    let pairScale := (L : ℝ) * unitScale
    let selfScale := (n : ℝ) * unitScale
    let meanBound := 1 + (n : ℝ) * (rho / (1 - omega)) /
      candidateScale + n + 2 * B
    let columnBound :=
      (k : ℝ) * mixedCandidateWeightedPerColorColumnBound
        (Label := Label) (β := β) (qstep := qstep) (r := r) n +
      ((mixedGraphAtomBound (Label := Label)
        (β := β) (qstep := qstep) (r := r) : ℝ) ^ k) * n + 1 +
      Fintype.card (Option Label)
    let deviation := FinitePartialResamplingNumerics.packingDeviation
      meanBound columnBound
    let sharpMean :=
      (mixedCandidateOrientedScale (Label := Label)
        (β := β) (qstep := qstep) (r := r) rho s omega C0 /
        (n : ℝ)) * (rho * s * n)
    ∃ choice : ∀ v (b : Fin B),
        G.MixedGraphPackedBlockState proposal edgeLabel qLaw R b,
      (∀ v b, 0 < G.mixedBlockProbability proposal edgeLabel qLaw R
        omega v b (choice v b)) ∧
      (∀ row : G.MixedBlockJointRow proposal edgeLabel qLaw R,
        FiniteCategoricalSelection.rowLoad
          (G.mixedBlockJointUse proposal edgeLabel qLaw R
            n candidateScale rho omega pairScale selfScale) row
          (fun source ↦ choice source.1 source.2) <
        FiniteCategoricalSelection.rowMean
          (fun source : G.V × Fin B ↦
            G.mixedBlockProbability proposal edgeLabel qLaw R
              omega source.1 source.2)
          (G.mixedBlockJointUse proposal edgeLabel qLaw R
            n candidateScale rho omega pairScale selfScale) row +
          deviation) ∧
      (∀ v,
        G.selectedTotalRawMixedBlockVariance
            proposal edgeLabel qLaw R rho omega choice v ≤
          sharpMean + (selfScale + (B : ℝ) * pairScale) * deviation) ∧
      (∀ v,
        (∑ e : G.StarEdge v, G.weight e.1 *
          (1 - min 1 (G.selectedMixedBlockTotalOptionMass
            proposal edgeLabel qLaw R rho omega choice e.1))) ≤
        (∑ e : G.StarEdge v, G.weight e.1 *
          max 0 (1 - G.mixedBlockTotalTarget proposal rho s e.1)) +
        t * G.starWeight v +
        ((B : ℝ) *
          (sharpMean + (selfScale + (B : ℝ) * pairScale) * deviation)) /
          (4 * t)) := by
  classical
  dsimp
  obtain ⟨choice, hsupport, hrows⟩ :=
    G.exists_mixedGraphSupportedBlockJointChoice
      proposal edgeLabel qLaw R hL hmult hn hk hq0 hqmarg
      hqsingle hqsum hs hqstep hr0 hleft homega0 homega1
      hrho hC0 hproposal0 hproposal hstar
  let candidateScale := (L : ℝ) *
    mixedCandidateOrientedScale (Label := Label)
      (β := β) (qstep := qstep) (r := r) rho s omega C0
  let unitScale := mixedBlockVarianceUnitScale (k := k) (s := s)
    (Label := Label) (β := β) (qstep := qstep) (r := r)
    n rho omega C0
  let pairScale := (L : ℝ) * unitScale
  let selfScale := (n : ℝ) * unitScale
  let meanBound := 1 + (n : ℝ) * (rho / (1 - omega)) /
    candidateScale + n + 2 * B
  let columnBound :=
    (k : ℝ) * mixedCandidateWeightedPerColorColumnBound
      (Label := Label) (β := β) (qstep := qstep) (r := r) n +
    ((mixedGraphAtomBound (Label := Label)
      (β := β) (qstep := qstep) (r := r) : ℝ) ^ k) * n + 1 +
    Fintype.card (Option Label)
  let deviation := FinitePartialResamplingNumerics.packingDeviation
    meanBound columnBound
  let sharpMean :=
    (mixedCandidateOrientedScale (Label := Label)
      (β := β) (qstep := qstep) (r := r) rho s omega C0 /
      (n : ℝ)) * (rho * s * n)
  have hunit : 0 < unitScale :=
    mixedBlockVarianceUnitScale_pos (Label := Label) (k := k)
      (s := s) (β := β) (qstep := qstep) (r := r)
      hn hk hs homega0 hrho hC0
  have hpair : 0 < pairScale := by
    dsimp [pairScale]
    exact mul_pos (by exact_mod_cast hL) hunit
  have hself : 0 < selfScale := by
    dsimp [selfScale]
    exact mul_pos (by exact_mod_cast hn) hunit
  have hvarianceRows : ∀ row : G.MixedBlockVarianceRow
      proposal edgeLabel qLaw R,
      FiniteCategoricalSelection.rowLoad
        (G.mixedBlockVarianceUse proposal edgeLabel qLaw R
          rho omega pairScale selfScale) row
        (fun source ↦ choice source.1 source.2) ≤
      FiniteCategoricalSelection.rowMean
        (fun source : G.V × Fin B ↦
          G.mixedBlockProbability proposal edgeLabel qLaw R
            omega source.1 source.2)
        (G.mixedBlockVarianceUse proposal edgeLabel qLaw R
          rho omega pairScale selfScale) row + deviation := by
    intro row
    have h := hrows (Sum.inl (Sum.inr row))
    change _ < _ at h
    exact h.le
  have hvariance := G.selectedTotalRawMixedBlockVariance_le_of_rowBounds
    proposal edgeLabel qLaw R rho omega pairScale selfScale deviation
    hpair hself choice hvarianceRows
  have hmean : ∀ v,
      G.meanTotalMixedBlockVariance
        proposal edgeLabel qLaw R rho omega v ≤ sharpMean := by
    intro v
    exact G.meanTotalMixedBlockVariance_le_sharp
      proposal edgeLabel qLaw R hn hq0 hqmarg hqsingle hqsum
      hs.le hqstep hr0 hleft homega0 homega1.le rho C0
      hrho.le hC0.le hproposal0 hproposal hmass hstar v
  have hbound : ∀ v,
      G.selectedTotalRawMixedBlockVariance
          proposal edgeLabel qLaw R rho omega choice v ≤
        sharpMean + (selfScale + (B : ℝ) * pairScale) * deviation := by
    intro v
    have hv := hvariance v
    have hm := hmean v
    nlinarith
  refine ⟨choice, hsupport, ?_, hbound, ?_⟩
  · exact hrows
  · intro v
    have hclip := G.selectedMixedBlockStarClippedResidual_le
      proposal edgeLabel qLaw R rho omega t ht choice v
    have hscaled := mul_le_mul_of_nonneg_left (hbound v)
      (Nat.cast_nonneg B)
    have hden : 0 ≤ 4 * t := by positivity
    have hdiv := div_le_div_of_nonneg_right hscaled hden
    linarith

end WeightedMultigraph

end
end WeightedEdgeColoring
