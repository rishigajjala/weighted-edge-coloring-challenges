import WeightedEdgeColoring.SubtwoMixedGraphBlockTargetFill
import WeightedEdgeColoring.SubtwoMixedGraphBlockTauUniformScalars

/-! Concrete full mixed words under the uniform joint-profile scalar event. -/

namespace WeightedEdgeColoring

open scoped BigOperators

noncomputable section

namespace WeightedMultigraph

/-- The graph-independent numerical event needed by the joint block selector. -/
def jointProfileUniformScalarEvent
    (Label : Type*) [Fintype Label] [DecidableEq Label]
    (B k L n : ℕ) (tau C0 D t eta : ℝ) : Prop :=
  let s := jointProfileS tau
  let beta := jointProfileBeta tau
  let qstep := jointProfileQ tau
  let r := jointProfileR tau
  let rho := jointProfileRho tau
  let omega := jointProfileOmega tau
  let A := mixedCandidateOrientedScale (Label := Label)
    (β := beta) (qstep := qstep) (r := r) rho s omega C0
  let U := mixedBlockVarianceUnitScale (k := k) (s := s)
    (Label := Label) (β := beta) (qstep := qstep) (r := r)
    n rho omega C0
  let scale := (L : ℝ) * A
  let meanBound := 1 + (n : ℝ) * (rho / (1 - omega)) /
    scale + n + 2 * B
  let columnBound :=
    (k : ℝ) * mixedCandidateWeightedPerColorColumnBound
      (Label := Label) (β := beta) (qstep := qstep) (r := r) n +
    ((mixedGraphAtomBound (Label := Label)
      (β := beta) (qstep := qstep) (r := r) : ℝ) ^ k) * n + 1 +
    Fintype.card (Option Label)
  let deviation := FinitePartialResamplingNumerics.packingDeviation
    meanBound columnBound
  scale / (n : ℝ) * deviation ≤ tau ^ 2 / 4 ∧
  rho / (1 - omega) + scale / (n : ℝ) * deviation ≤
    1 - tau / 2 ∧
  scale / (n : ℝ) * deviation + 2 * beta ≤
    (1 - rho / (1 - omega)) * r ∧
  (k : ℝ) * deviation ≤ eta * n ∧
  t * n + (B : ℝ) *
    (A * (rho * s) + ((n : ℝ) + B * L) * U * deviation) /
      (4 * t) ≤
    (t + D * (A * (rho * s)) / (4 * t) + eta) * n

variable (G : WeightedMultigraph)
variable {B k : ℕ} {Label : Type*} [Fintype Label] [DecidableEq Label]
variable (proposal : G.E → (Fin B × Fin k) → ℝ)
variable (edgeLabel : ∀ v : G.V, G.StarEdge v → Label)
variable (qLaw : ∀ v : G.V, (Fin B × Fin k) →
  Finset (G.StarEdge v) → ℝ)
variable {tau : ℝ} {hβ : 0 < jointProfileBeta tau}
  {hr : 0 < jointProfileR tau}
variable (R : ∀ v c label,
  G.BoundedProfileRealization
    (G.conditionalEndpointProposal (edgeLabel v)
      (fun e : G.StarEdge v ↦ proposal e.1 c) (qLaw v c) label)
    (jointProfileS tau) (jointProfileBeta tau)
      (jointProfileQ tau) (jointProfileR tau) hβ hr)

theorem exists_fullMixedWord_jointProfile_uniform
    {L n : ℕ} {C0 D t eta epsMix : ℝ}
    (htau0 : 0 < tau) (htau1 : tau ≤ 1 / 4)
    (hL : 0 < L) (hmult : G.PairMultiplicityAtMost L)
    (hn : 0 < n) (hB : 0 < B) (hk : 0 < k)
    (hq0 : ∀ v c S, 0 ≤ qLaw v c S)
    (hqmarg : ∀ v c (f : G.StarEdge v),
      (∑ S, if f ∈ S then qLaw v c S else 0) = proposal f.1 c)
    (hqsingle : ∀ v c S, qLaw v c S ≠ 0 → S ≠ ∅ →
      ∃ label : Label, ∀ f ∈ S, edgeLabel v f = label)
    (hqsum : ∀ v c, ∑ S, qLaw v c S = 1)
    (hC0 : 0 < C0) (ht : 0 < t) (heps : 0 ≤ epsMix)
    (hproposal0 : ∀ e c, 0 ≤ proposal e c)
    (hproposal : ∀ e c, proposal e c ≤ C0 / (n : ℝ))
    (hmass : ∀ e, ∑ c : Fin B × Fin k, proposal e c ≤ 1)
    (hdeficit : ∀ v,
      G.proposalDeficit
        (fun e c ↦ proposal e (finProdFinEquiv.symm c)) v ≤
          epsMix * n)
    (hstar : ∀ v, G.starWeight v ≤ n)
    (hscalar : jointProfileUniformScalarEvent Label B k L n
      tau C0 D t eta) :
    let A := mixedCandidateOrientedScale (Label := Label)
      (β := jointProfileBeta tau) (qstep := jointProfileQ tau)
      (r := jointProfileR tau) (jointProfileRho tau)
      (jointProfileS tau) (jointProfileOmega tau) C0
    let scale := (L : ℝ) * A
    let meanBound := 1 + (n : ℝ) *
      (jointProfileRho tau / (1 - jointProfileOmega tau)) /
      scale + n + 2 * B
    let columnBound :=
      (k : ℝ) * mixedCandidateWeightedPerColorColumnBound
        (Label := Label) (β := jointProfileBeta tau)
        (qstep := jointProfileQ tau) (r := jointProfileR tau) n +
      ((mixedGraphAtomBound (Label := Label)
        (β := jointProfileBeta tau) (qstep := jointProfileQ tau)
        (r := jointProfileR tau) : ℝ) ^ k) * n + 1 +
      Fintype.card (Option Label)
    let deviation := FinitePartialResamplingNumerics.packingDeviation
      meanBound columnBound
    ∃ selected : ∀ v : G.V, ∀ c : Fin B × Fin k,
        G.MixedGraphAtom proposal edgeLabel qLaw R v c,
      let fullChoice : ∀ v : G.V,
          G.MixedGraphPackedState proposal edgeLabel qLaw R :=
        fun v ↦ G.encodeMixedGraphWord proposal edgeLabel qLaw R
          v (selected v)
      (∀ c (row : G.MixedCandidateRowAt proposal edgeLabel qLaw R c),
        G.selectedMixedCandidateCapacityLoad
          proposal edgeLabel qLaw R (jointProfileRho tau)
          (jointProfileOmega tau) fullChoice c row < 1 - tau / 2) ∧
      (∀ v c,
        G.selectedMixedNormalizedTinyReservoirLoad
          proposal edgeLabel qLaw R (jointProfileRho tau)
          (jointProfileOmega tau) fullChoice v c <
        jointProfileRho tau / (1 - jointProfileOmega tau) *
          G.selectedMixedConcreteReservoirSize
            proposal edgeLabel qLaw R fullChoice v c +
          scale / (n : ℝ) * deviation) ∧
      (∀ v label,
        G.selectedMixedEndpointLabelCount
          proposal edgeLabel qLaw R fullChoice v label <
        (∑ c : Fin B × Fin k,
          subsetLabelMass (edgeLabel v) (qLaw v c) label) +
        ((B : ℝ) * k) * tau + eta * n) ∧
      (∀ v,
        G.weightedResidualStar
          (G.selectedMixedResidualOptionMass
            proposal edgeLabel qLaw R (jointProfileRho tau)
            (jointProfileOmega tau) fullChoice) v ≤
        (4 * tau + epsMix + t +
          D * (A * (jointProfileRho tau * jointProfileS tau)) /
            (4 * t) + eta) * n) := by
  classical
  rcases jointProfile_parameters htau0 htau1 with
    ⟨hs, _hbeta, hq, hrpos, homega0, _, hleft, _, hrho, _, _⟩
  have homega1 : jointProfileOmega tau < 1 := by
    unfold jointProfileOmega
    linarith
  dsimp only [jointProfileUniformScalarEvent] at hscalar
  dsimp only at hscalar ⊢
  rcases hscalar with ⟨_, hrate, _, hlabelError, hselectionError⟩
  obtain ⟨selected, hcap, hrelative, hlabel, hresidual⟩ :=
    G.exists_fullMixedWord_sharpResidual
      proposal edgeLabel qLaw R hL hmult hn hB hk
      hq0 hqmarg hqsingle hqsum hs hq.le hrpos.le hleft
      homega0 homega1 hrho hC0 hproposal0 hproposal hmass hstar
      t ht
  refine ⟨selected, ?_, hrelative, ?_, ?_⟩
  · intro c row
    exact lt_of_lt_of_le (hcap c row) hrate
  · intro v label
    have hv := hlabel v label
    simp only [jointProfileOmega] at hv hlabelError
    linarith
  · intro v
    have htarget := G.mixedBlockTargetDeficit_le_jointProfile_of_proposalDeficit
      proposal htau0.le htau1 hmass v
    have htargetN := mul_le_mul_of_nonneg_left (hstar v)
      (by positivity : (0 : ℝ) ≤ 4 * tau)
    have hproposalDeficit := hdeficit v
    have htn := mul_le_mul_of_nonneg_left (hstar v) ht.le
    have hv := hresidual v
    let U := mixedBlockVarianceUnitScale (k := k)
      (s := jointProfileS tau) (Label := Label)
      (β := jointProfileBeta tau) (qstep := jointProfileQ tau)
      (r := jointProfileR tau) n (jointProfileRho tau)
      (jointProfileOmega tau) C0
    have hE : (n : ℝ) * U + (B : ℝ) * ((L : ℝ) * U) =
        ((n : ℝ) + B * L) * U := by ring
    rw [hE] at hv
    linarith [htarget, htargetN, hproposalDeficit, htn, hselectionError]

end WeightedMultigraph

end
end WeightedEdgeColoring
