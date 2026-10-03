import WeightedEdgeColoring.SubtwoMixedGraphBlockUniformDecoder
import WeightedEdgeColoring.SubtwoMixedGraphBlockDecoderScalars
import WeightedEdgeColoring.SubtwoMixedGraphBlockOuterCaps
import WeightedEdgeColoring.SubtwoMixedGraphBlockInitialSlotEventual

/-! A single graph-independent threshold for every numerical input to the
physical mixed-block decoder. -/

namespace WeightedEdgeColoring

noncomputable section

namespace WeightedMultigraph

theorem mixedGraph_eventually_uniformPhysicalNumerics
    {Label : Type*} [Fintype Label] [DecidableEq Label]
    {k mult Lbucket : ℕ}
    {tau C0 t eta alpha delta traceEps : ℝ}
    (hk : 0 < k) (hmult : 0 < mult)
    (htau0 : 0 < tau) (htau1 : tau ≤ 1 / 4)
    (hC0 : 0 < C0) (ht : 0 < t) (heta : 0 < eta)
    (hdyadicCover :
      1 ≤ dyadicScale (jointProfileBeta tau) Lbucket)
    (halpha : 0 < alpha) (halphaSmall : alpha ≤ 1 / 100000)
    (halphaDelta : alpha ≤ delta / 96)
    (hdelta0 : 0 < delta) (hdelta1 : delta ≤ 1)
    (hdeltaHalf : delta = 1 / 2)
    (htraceEps0 : 0 < traceEps) (htraceEps1 : traceEps ≤ 1) :
    ∃ n0 : ℕ, ∀ n B : ℕ, n0 ≤ n → B * k ≤ 4 * n →
      let m := dyadicSimpleRoot n
      let beta := jointProfileBeta tau
      let qstep := jointProfileQ tau
      let r := jointProfileR tau
      let rho := jointProfileRho tau
      let s := jointProfileS tau
      let omega := jointProfileOmega tau
      let places := explicitLargeSlotBound beta qstep r
      let scale := mixedGraphCandidateCapacityScale (Label := Label)
        (β := beta) (qstep := qstep) (r := r) rho s omega C0
      let Acoef := boundedMultiplicityDyadicFixedCodegreeCoefficient
        mult places scale
      let Ecoef := boundedMultiplicityDyadicSupportCoefficient beta (tau / 4)
      let Ccoef := 4 * boundedMultiplicityDyadicChoiceCoefficient
        places beta (tau / 4)
      let N := dyadicSimpleQuantizationScale m
      let reserve := dyadicSimpleReserveScale m
      let lambda := dyadicSimpleCodegreeScale Acoef m
      let E := Ecoef * m ^ 20
      let C := Ccoef * m ^ 20
      let S0 :=
        RankThreeOptionSystem.OriginalIterationState.fixedSlackPaddedSlotTarget
          (tau / 8) (N - C)
      let K := dyadicSimpleEndpointBlockScale 1 m
      let steps := variableSlackSteps alpha (tau / 8) traceEps lambda
      MixedMaskedClosedScalars beta alpha (tau / 8) delta
        N C S0 lambda Lbucket K steps ∧
      (1 - (1 - delta) * variableSlackA alpha (tau / 8) lambda / 8) ^
        steps ≤ traceEps ∧
      jointProfileUniformScalarEvent Label B k mult n
        tau C0 ((4 : ℝ) / k) t eta ∧
      C ≤ N ∧ (C : ℝ) + 1 ≤ (tau / 8) * N ∧
      0 < N ∧ 0 < reserve ∧
      (N : ℝ) * ((places : ℝ) * scale / n) ≤ lambda ∧
      scale / n ≤ 1 / (reserve : ℝ) ∧
      (N : ℝ) / reserve ≤ lambda ∧
      (mult : ℝ) * N / reserve ≤ lambda ∧
      2 * ((n : ℝ) / beta / (1 - tau / 4) +
        1 + reserve) ≤ E ∧
      B * k * places * places + E ≤ C := by
  rcases jointProfile_parameters htau0 htau1 with
    ⟨hs, hbeta, hq, hr, homega, _, _, _, hrho, _, _⟩
  have hextraGamma : tau / 4 < 1 := by linarith
  have hscale0 : 0 ≤ mixedGraphCandidateCapacityScale
      (Label := Label) (β := jointProfileBeta tau)
      (qstep := jointProfileQ tau) (r := jointProfileR tau)
      (jointProfileRho tau) (jointProfileS tau)
      (jointProfileOmega tau) C0 := by
    unfold mixedGraphCandidateCapacityScale
    positivity
  let places := explicitLargeSlotBound
    (jointProfileBeta tau) (jointProfileQ tau) (jointProfileR tau)
  let scale := mixedGraphCandidateCapacityScale (Label := Label)
    (β := jointProfileBeta tau) (qstep := jointProfileQ tau)
    (r := jointProfileR tau)
    (jointProfileRho tau) (jointProfileS tau)
    (jointProfileOmega tau) C0
  let Acoef := boundedMultiplicityDyadicFixedCodegreeCoefficient
    mult places scale
  let Ccoef := 4 * boundedMultiplicityDyadicChoiceCoefficient
    places (jointProfileBeta tau) (tau / 4)
  have hAcoef : 0 < Acoef := by
    unfold Acoef boundedMultiplicityDyadicFixedCodegreeCoefficient
      boundedMultiplicityDyadicCodegreeCoefficient
    omega
  have hD : (0 : ℝ) ≤ 4 / k := by positivity
  obtain ⟨nd, hd⟩ := mixedGraph_eventually_blockDecoderScalars
    (Label := Label) (k := k) (mult := mult)
    (L := Lbucket) (A := Acoef) (Ccoef := Ccoef)
    (tau := tau) (C0 := C0) (D := (4 : ℝ) / k)
    (t := t) (eta := eta) (alpha := alpha) (delta := delta)
    (traceEps := traceEps)
    htau0 htau1 hmult hC0 hD ht heta
    hdyadicCover hAcoef halpha halphaSmall halphaDelta
    hdelta0 hdelta1 hdeltaHalf htraceEps0 htraceEps1
  obtain ⟨no, ho⟩ := mixedGraph_eventually_blockOuterCaps
    (Label := Label) (k := k) (mult := mult)
    (β := jointProfileBeta tau) (qstep := jointProfileQ tau)
    (r := jointProfileR tau) (rho := jointProfileRho tau)
    (s := jointProfileS tau) (omega := jointProfileOmega tau)
    (C0 := C0) (extraGamma := tau / 4)
    hbeta hextraGamma hscale0
  obtain ⟨ni, hi⟩ := mixedGraph_eventually_blockInitialSlotLoss
    (tau := tau) (Ccoef := Ccoef) htau0 htau1
  refine ⟨max (2 ^ 20) (max nd (max no ni)), ?_⟩
  intro n B hn hpalette
  have hbase : 2 ^ 20 ≤ n :=
    (le_max_left (2 ^ 20) (max nd (max no ni))).trans hn
  have hinner : max nd (max no ni) ≤ n :=
    (le_max_right (2 ^ 20) (max nd (max no ni))).trans hn
  have hnd : nd ≤ n := (le_max_left nd (max no ni)).trans hinner
  have hno : no ≤ n :=
    (le_max_left no ni).trans ((le_max_right nd (max no ni)).trans hinner)
  have hni : ni ≤ n :=
    (le_max_right no ni).trans ((le_max_right nd (max no ni)).trans hinner)
  have hB : (B : ℝ) ≤ ((4 : ℝ) / k) * n :=
    blockCount_le_of_colorBudget hk hpalette
  obtain ⟨hdyadic, hscalar⟩ := hd n B hnd hB
  obtain ⟨hcodeg, hpair, hextraCodeg, hpairCodeg, hE, hchoice⟩ :=
    ho n B hno hpalette
  obtain ⟨hCN, hloss⟩ := hi n hni
  have hm1 : 1 ≤ dyadicSimpleRoot n := by
    apply le_dyadicSimpleRoot_of_pow_le
    have hn1 : 1 ≤ n := by omega
    simpa using hn1
  have hN : 0 < dyadicSimpleQuantizationScale (dyadicSimpleRoot n) := by
    unfold dyadicSimpleQuantizationScale
    positivity
  have hreserve : 0 < dyadicSimpleReserveScale (dyadicSimpleRoot n) := by
    unfold dyadicSimpleReserveScale
    positivity
  dsimp only
  exact ⟨hdyadic.1, hdyadic.2, hscalar, hCN, hloss,
    hN, hreserve, hcodeg, hpair, hextraCodeg, hpairCodeg, hE, hchoice⟩

end WeightedMultigraph

end
end WeightedEdgeColoring
