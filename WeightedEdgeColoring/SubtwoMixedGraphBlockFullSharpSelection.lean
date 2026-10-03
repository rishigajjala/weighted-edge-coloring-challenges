import WeightedEdgeColoring.SubtwoMixedGraphBlockSharpResidual
import WeightedEdgeColoring.SubtwoMixedGraphBlockPhysicalSelection

/-! A sharp joint block choice is an actual mixed full word. -/

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

theorem exists_fullMixedWord_sharpResidual
    {L n : ℕ} (hL : 0 < L) (hmult : G.PairMultiplicityAtMost L)
    (hn : 0 < n) (hB : 0 < B) (hk : 0 < k)
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
    let A := mixedCandidateOrientedScale (Label := Label)
      (β := β) (qstep := qstep) (r := r) rho s omega C0
    let scale := (L : ℝ) * A
    let U := mixedBlockVarianceUnitScale (k := k) (s := s)
      (Label := Label) (β := β) (qstep := qstep) (r := r)
      n rho omega C0
    let pairScale := (L : ℝ) * U
    let selfScale := (n : ℝ) * U
    let meanBound := 1 + (n : ℝ) * (rho / (1 - omega)) /
      scale + n + 2 * B
    let columnBound :=
      (k : ℝ) * mixedCandidateWeightedPerColorColumnBound
        (Label := Label) (β := β) (qstep := qstep) (r := r) n +
      ((mixedGraphAtomBound (Label := Label)
        (β := β) (qstep := qstep) (r := r) : ℝ) ^ k) * n + 1 +
      Fintype.card (Option Label)
    let deviation := FinitePartialResamplingNumerics.packingDeviation
      meanBound columnBound
    let sharpMean := A * (rho * s)
    ∃ selected : ∀ v : G.V, ∀ c : Fin B × Fin k,
        G.MixedGraphAtom proposal edgeLabel qLaw R v c,
      let fullChoice : ∀ v : G.V,
          G.MixedGraphPackedState proposal edgeLabel qLaw R :=
        fun v ↦ G.encodeMixedGraphWord proposal edgeLabel qLaw R
          v (selected v)
      (∀ c (row : G.MixedCandidateRowAt proposal edgeLabel qLaw R c),
        G.selectedMixedCandidateCapacityLoad
          proposal edgeLabel qLaw R rho omega fullChoice c row <
          rho / (1 - omega) + scale / (n : ℝ) * deviation) ∧
      (∀ v c,
        G.selectedMixedNormalizedTinyReservoirLoad
          proposal edgeLabel qLaw R rho omega fullChoice v c <
        rho / (1 - omega) *
          G.selectedMixedConcreteReservoirSize
            proposal edgeLabel qLaw R fullChoice v c +
          scale / (n : ℝ) * deviation) ∧
      (∀ v label,
        G.selectedMixedEndpointLabelCount
          proposal edgeLabel qLaw R fullChoice v label <
        (∑ c : Fin B × Fin k,
          subsetLabelMass (edgeLabel v) (qLaw v c) label) +
        ((B : ℝ) * k) * omega + (k : ℝ) * deviation) ∧
      (∀ v,
        G.weightedResidualStar
          (G.selectedMixedResidualOptionMass
            proposal edgeLabel qLaw R rho omega fullChoice) v ≤
        (∑ e : G.StarEdge v, G.weight e.1 *
          max 0 (1 - G.mixedBlockTotalTarget proposal rho s e.1)) +
        t * G.starWeight v +
        (B : ℝ) *
          (sharpMean + (selfScale + (B : ℝ) * pairScale) * deviation) /
          (4 * t)) := by
  classical
  dsimp only
  obtain ⟨choice, hsupport, hrows, _hvariance, hresidual⟩ :=
    G.exists_mixedGraphSupportedBlockChoice_sharpResidual
      proposal edgeLabel qLaw R hL hmult hn hk hq0 hqmarg
      hqsingle hqsum hs hqstep hr0 hleft homega0 homega1
      hrho hC0 hproposal0 hproposal hmass hstar t ht
  have hA : 0 < mixedCandidateOrientedScale (Label := Label)
      (β := β) (qstep := qstep) (r := r) rho s omega C0 :=
    mixedCandidateOrientedScale_pos hrho hs homega0 hC0
  have hscale : 0 < (L : ℝ) *
      mixedCandidateOrientedScale (Label := Label)
        (β := β) (qstep := qstep) (r := r) rho s omega C0 :=
    mul_pos (by exact_mod_cast hL) hA
  have hn0 : (n : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hn)
  have hmeanEq :
      mixedCandidateOrientedScale (Label := Label)
          (β := β) (qstep := qstep) (r := r) rho s omega C0 /
          (n : ℝ) * (rho * s * n) =
        mixedCandidateOrientedScale (Label := Label)
          (β := β) (qstep := qstep) (r := r) rho s omega C0 *
          (rho * s) := by
    field_simp
  rw [hmeanEq] at hresidual
  exact G.exists_fullMixedWord_of_selectedBlocks
    proposal edgeLabel qLaw R hB hk hn
    ((L : ℝ) * mixedCandidateOrientedScale (Label := Label)
      (β := β) (qstep := qstep) (r := r) rho s omega C0)
    rho omega
    ((L : ℝ) * mixedBlockVarianceUnitScale (k := k) (s := s)
      (Label := Label) (β := β) (qstep := qstep) (r := r)
      n rho omega C0)
    ((n : ℝ) * mixedBlockVarianceUnitScale (k := k) (s := s)
      (Label := Label) (β := β) (qstep := qstep) (r := r)
      n rho omega C0)
    (FinitePartialResamplingNumerics.packingDeviation
      (1 + (n : ℝ) * (rho / (1 - omega)) /
        ((L : ℝ) * mixedCandidateOrientedScale (Label := Label)
          (β := β) (qstep := qstep) (r := r) rho s omega C0) +
        n + 2 * B)
      ((k : ℝ) * mixedCandidateWeightedPerColorColumnBound
        (Label := Label) (β := β) (qstep := qstep) (r := r) n +
      ((mixedGraphAtomBound (Label := Label)
        (β := β) (qstep := qstep) (r := r) : ℝ) ^ k) * n + 1 +
      Fintype.card (Option Label)))
    hscale hq0 hqmarg hqsingle hqsum hs.le hqstep hr0
    hleft homega0 homega1 hrho.le hproposal0 choice hsupport
    hrows _ hresidual

end WeightedMultigraph

end
end WeightedEdgeColoring
