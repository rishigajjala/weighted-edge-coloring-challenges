import WeightedEdgeColoring.SubtwoMixedGraphBlockTauUniformScalars
import WeightedEdgeColoring.SubtwoMixedGraphDyadicEventualScalars

/-! One graph-independent threshold for the block selector and dyadic rounds. -/

namespace WeightedEdgeColoring

open RankThreeOptionSystem.OriginalIterationState

noncomputable section

namespace WeightedMultigraph

theorem mixedGraph_eventually_blockDecoderScalars
    {Label : Type*} [Fintype Label] [DecidableEq Label]
    {k mult L A Ccoef : ℕ}
    {tau C0 D t eta alpha delta traceEps : ℝ}
    (htau0 : 0 < tau) (htau1 : tau ≤ 1 / 4)
    (hmult : 0 < mult) (hC0 : 0 < C0) (hD : 0 ≤ D)
    (ht : 0 < t) (heta : 0 < eta)
    (hdyadicCover : 1 ≤ dyadicScale (jointProfileBeta tau) L)
    (hA : 0 < A)
    (halpha : 0 < alpha) (halphaSmall : alpha ≤ 1 / 100000)
    (halphaDelta : alpha ≤ delta / 96)
    (hdelta0 : 0 < delta) (hdelta1 : delta ≤ 1)
    (hdeltaHalf : delta = 1 / 2)
    (htraceEps0 : 0 < traceEps) (htraceEps1 : traceEps ≤ 1) :
    ∃ n0 : ℕ, ∀ n B : ℕ, n0 ≤ n → (B : ℝ) ≤ D * n →
      (let m := dyadicSimpleRoot n
       let N := dyadicSimpleQuantizationScale m
       let C := Ccoef * m ^ 20
       let d0 := N - C
       let S0 := fixedSlackPaddedSlotTarget (tau / 8) d0
       let lambda := dyadicSimpleCodegreeScale A m
       let K := dyadicSimpleEndpointBlockScale 1 m
       let steps := variableSlackSteps alpha (tau / 8) traceEps lambda
       MixedMaskedClosedScalars (jointProfileBeta tau)
         alpha (tau / 8) delta N C S0 lambda L K steps ∧
       (1 - (1 - delta) * variableSlackA alpha (tau / 8) lambda / 8) ^
         steps ≤ traceEps) ∧
      (let s := jointProfileS tau
       let beta := jointProfileBeta tau
       let qstep := jointProfileQ tau
       let r := jointProfileR tau
       let rho := jointProfileRho tau
       let omega := jointProfileOmega tau
       let A0 := mixedCandidateOrientedScale (Label := Label)
         (β := beta) (qstep := qstep) (r := r) rho s omega C0
       let U := mixedBlockVarianceUnitScale (k := k) (s := s)
         (Label := Label) (β := beta) (qstep := qstep) (r := r)
         n rho omega C0
       let scale := (mult : ℝ) * A0
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
         (A0 * (rho * s) + ((n : ℝ) + B * mult) * U * deviation) /
           (4 * t) ≤
         (t + D * (A0 * (rho * s)) / (4 * t) + eta) * n) := by
  have hgamma0 : 0 < tau / 8 := by positivity
  have hgammaHalf : tau / 8 ≤ 1 / 2 := by linarith
  obtain ⟨nd, hd⟩ := mixedGraph_eventually_dyadicClosedScalars
    (β := jointProfileBeta tau) (alpha := alpha) (gamma := tau / 8)
    (delta := delta) (traceEps := traceEps)
    (A := A) (Ccoef := Ccoef) (L := L)
    hdyadicCover hA halpha halphaSmall halphaDelta
    hgamma0 hgammaHalf hdelta0 hdelta1 hdeltaHalf
    htraceEps0 htraceEps1
  obtain ⟨ns, hs⟩ := mixedBlock_jointProfile_errors_eventually
    (Label := Label) (k := k) (L := mult)
    (tau := tau) (C0 := C0) (D := D) (t := t) (eta := eta)
    htau0 htau1 hmult hC0 hD ht heta
  refine ⟨max nd ns, ?_⟩
  intro n B hn hB
  exact ⟨hd n ((le_max_left nd ns).trans hn),
    hs n B ((le_max_right nd ns).trans hn) hB⟩

end WeightedMultigraph

end
end WeightedEdgeColoring
