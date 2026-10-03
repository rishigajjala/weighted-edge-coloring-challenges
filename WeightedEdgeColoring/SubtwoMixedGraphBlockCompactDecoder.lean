import WeightedEdgeColoring.SubtwoMixedGraphBlockColorTransport
import WeightedEdgeColoring.SubtwoMixedGraphJointSelectedSupport

/-! Compact physical output of the uniform selected mixed decoder. -/

namespace WeightedEdgeColoring

open scoped BigOperators

noncomputable section

namespace WeightedMultigraph

theorem mixedGraph_eventually_compactPhysicalDecoder
    {Label : Type*} [Fintype Label] [DecidableEq Label]
    {k mult Lbucket : ℕ}
    {tau C0 t eta epsMix alpha delta traceEps : ℝ}
    (hk : 0 < k) (hmult0 : 0 < mult)
    (htau0 : 0 < tau) (htau1 : tau ≤ 1 / 4)
    (hC0 : 0 < C0) (ht : 0 < t) (heta : 0 < eta)
    (hepsMix : 0 ≤ epsMix)
    (hdyadicCover :
      1 ≤ dyadicScale (jointProfileBeta tau) Lbucket)
    (hdyadicTop : dyadicScale (jointProfileBeta tau) Lbucket < 2)
    (halpha : 0 < alpha) (halphaSmall : alpha ≤ 1 / 100000)
    (halphaDelta : alpha ≤ delta / 96)
    (hdelta0 : 0 < delta) (hdelta1 : delta ≤ 1)
    (hdeltaHalf : delta = 1 / 2)
    (htraceEps0 : 0 < traceEps) (htraceEps1 : traceEps ≤ 1) :
    ∃ n0 : ℕ, ∀ (n B : ℕ), n0 ≤ n → B * k ≤ 4 * n →
      ∀ (G : WeightedMultigraph)
        (proposal : G.E → (Fin B × Fin k) → ℝ)
        (edgeLabel : ∀ v : G.V, G.StarEdge v → Label)
        (qLaw : ∀ v : G.V, (Fin B × Fin k) →
          Finset (G.StarEdge v) → ℝ)
        (hβ : 0 < jointProfileBeta tau)
        (hr : 0 < jointProfileR tau)
        (R : ∀ v c label,
          G.BoundedProfileRealization
            (G.conditionalEndpointProposal (edgeLabel v)
              (fun e : G.StarEdge v ↦ proposal e.1 c)
              (qLaw v c) label)
            (jointProfileS tau) (jointProfileBeta tau)
              (jointProfileQ tau) (jointProfileR tau) hβ hr),
        let m := dyadicSimpleRoot n
        let beta := jointProfileBeta tau
        let qstep := jointProfileQ tau
        let r := jointProfileR tau
        let rho := jointProfileRho tau
        let s := jointProfileS tau
        let omega := jointProfileOmega tau
        let places := explicitLargeSlotBound beta qstep r
        let capacityScale := mixedGraphCandidateCapacityScale (Label := Label)
          (β := beta) (qstep := qstep) (r := r) rho s omega C0
        let Acoef := boundedMultiplicityDyadicFixedCodegreeCoefficient
          mult places capacityScale
        let Ecoef := boundedMultiplicityDyadicSupportCoefficient
          beta (tau / 4)
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
        let L := Lbucket
        let D := (4 : ℝ) / k
        G.PairMultiplicityAtMost mult → (hB : 0 < B) →
        (∀ v c S, 0 ≤ qLaw v c S) →
        (∀ v c (f : G.StarEdge v),
          (∑ S, if f ∈ S then qLaw v c S else 0) = proposal f.1 c) →
        (∀ v c S, qLaw v c S ≠ 0 → S ≠ ∅ →
          ∃ label : Label, ∀ f ∈ S, edgeLabel v f = label) →
        (∀ v c, ∑ S, qLaw v c S = 1) →
        (∀ e c, 0 ≤ proposal e c) →
        (∀ e c, proposal e c ≤ C0 / (n : ℝ)) →
        (∀ e, ∑ c : Fin B × Fin k, proposal e c ≤ 1) →
        (∀ v,
          G.proposalDeficit
            (fun e c ↦ proposal e (finProdFinEquiv.symm c)) v ≤
              epsMix * n) →
        (∀ v, G.starWeight v ≤ n) →
    let A := mixedCandidateOrientedScale (Label := Label)
      (β := jointProfileBeta tau) (qstep := jointProfileQ tau)
      (r := jointProfileR tau) (jointProfileRho tau)
      (jointProfileS tau) (jointProfileOmega tau) C0
    let residualRate := 4 * tau + epsMix + t +
      ((4 : ℝ) / k) *
        (A * (jointProfileRho tau * jointProfileS tau)) /
        (4 * t) + eta
    ∃ (F : Finset G.E) (color : G.E → Fin (B * k))
      (selectedLabel : G.V → Fin (B * k) → Option Label),
      G.IsFeasibleOn F color ∧
      (∀ e ∈ F, 0 < proposal e (finProdFinEquiv.symm (color e))) ∧
      (∀ e ∈ F, ∀ v (hinc : G.Inc v e),
        selectedLabel v (color e) = some (edgeLabel v ⟨e, hinc⟩)) ∧
      (∀ v label,
        ((Finset.univ.filter (fun c : Fin (B * k) ↦
          selectedLabel v c = some label)).card : ℝ) <
        (∑ c : Fin B × Fin k,
          subsetLabelMass (edgeLabel v) (qLaw v c) label) +
        ((B : ℝ) * k) * tau + eta * n) ∧
      (∀ v,
        (∑ e ∈ Finset.univ \ F,
          if G.Inc v e then G.weight e else 0) ≤
        traceEps * n +
          (((Lbucket + 1) * (K - 1) : ℕ) : ℝ) +
          (4 / (1 - tau / 4) + 1) * (residualRate * n) +
          8 * (1 + (reserve : ℝ)) +
          2 * jointProfileBeta tau) := by
  classical
  obtain ⟨n0, hN0⟩ := mixedGraph_eventually_uniformPhysicalDecoder
    (Label := Label) (k := k) (mult := mult) (Lbucket := Lbucket)
    (tau := tau) (C0 := C0) (t := t) (eta := eta)
    (epsMix := epsMix) (alpha := alpha) (delta := delta)
    (traceEps := traceEps)
    hk hmult0 htau0 htau1 hC0 ht heta hepsMix
    hdyadicCover hdyadicTop halpha halphaSmall halphaDelta
    hdelta0 hdelta1 hdeltaHalf htraceEps0 htraceEps1
  refine ⟨n0, ?_⟩
  intro n B hn hpalette G proposal edgeLabel qLaw hβ hr R
  dsimp only
  intro hmult hB hq0 hqmarg hqsingle hqsum hproposal0
    hproposal hmass hdeficit hstar
  obtain ⟨selected, hlabel, M, hM, decision, hpositive,
    hfeasible, hresidual⟩ :=
    hN0 n B hn hpalette G proposal edgeLabel qLaw hβ hr R
      hmult hB hq0 hqmarg hqsingle hqsum hproposal0
      hproposal hmass hdeficit hstar
  let choice : ∀ v : G.V,
      G.MixedGraphPackedState proposal edgeLabel qLaw R :=
    fun v ↦ G.encodeMixedGraphWord proposal edgeLabel qLaw R v (selected v)
  let bucket := dyadicBucket (jointProfileBeta tau) Lbucket G.weight
  let residual := G.selectedMixedLargeResidual proposal edgeLabel qLaw R
    (jointProfileRho tau) (jointProfileOmega tau) choice
  let x := G.selectedMixedNormalizedLargeOptionMass
    proposal edgeLabel qLaw R
    (jointProfileRho tau) (jointProfileOmega tau) choice
  let places := explicitLargeSlotBound (jointProfileBeta tau)
    (jointProfileQ tau) (jointProfileR tau)
  let O := G.selectedDyadicOrdinaryBaseOptionsAny places
    (dyadicSimpleQuantizationScale (dyadicSimpleRoot n)) bucket
    (tau / 4) (dyadicSimpleReserveScale (dyadicSimpleRoot n))
    residual x M
  let OFin := O.map
    (OrdinarySlotChoice.colorEquiv
      (Fintype.equivFin (Fin B × Fin k))).toEmbedding
  let hO := G.selectedDyadicOrdinaryBaseOptionsAny_isPartialMatching
    places (dyadicSimpleQuantizationScale (dyadicSimpleRoot n)) bucket
    (tau / 4) (dyadicSimpleReserveScale (dyadicSimpleRoot n))
    residual x M hM
  let hOFin := ordinarySlotChoice_colorEquiv_isPartialMatching
    G.fst G.snd places (Fintype.equivFin (Fin B × Fin k)) O hO
  let T := G.selectedMixedTinyEdges (β := jointProfileBeta tau)
  let jointColor := G.ordinaryTinyJointColor
    (by simpa using Nat.mul_pos hB hk)
    OFin hOFin T decision
  let F := G.ordinarySelectedEdges OFin ∪
    G.tinyDecisionColoredEdges T decision
  let color : G.E → Fin (B * k) :=
    fun e ↦ mixedBlockPaletteEquiv B k (jointColor e)
  let selectedLabel : G.V → Fin (B * k) → Option Label :=
    fun v c ↦ G.decodeMixedGraphLabel proposal edgeLabel qLaw R
      v (choice v) (finProdFinEquiv.symm c)
  refine ⟨F, color, selectedLabel, ?_, ?_, ?_, ?_, ?_⟩
  · exact G.isFeasibleOn_flattenMixedBlockColor F jointColor hfeasible
  · intro e he
    have hColor : 0 < Fintype.card (Fin B × Fin k) := by
      simpa using Nat.mul_pos hB hk
    have hs := jointProfile_parameters htau0 htau1
    rcases hs with ⟨hs, _, hq, hr0, homega, _, hleft, _, hrho, _, _⟩
    have hdisj := G.selectedMixedRelabeledOrdinary_disjoint_tiny
      proposal edgeLabel qLaw R
      (jointProfileRho tau) (jointProfileOmega tau) choice
      bucket (tau / 4) (dyadicSimpleReserveScale (dyadicSimpleRoot n))
      (dyadicSimpleQuantizationScale (dyadicSimpleRoot n)) M
    have hOpos : ∀ o ∈ OFin,
        0 < x o.job ((Fintype.equivFin (Fin B × Fin k)).symm o.color)
          o.leftPlace o.rightPlace := by
      intro o ho
      exact G.selectedDyadicOrdinaryBaseOptionsAny_relabel_mass_pos
        places (dyadicSimpleQuantizationScale (dyadicSimpleRoot n))
        bucket (tau / 4) (dyadicSimpleReserveScale (dyadicSimpleRoot n))
        residual x M o ho
    have hsupport := G.selectedMixedJointColor_support
      proposal edgeLabel qLaw R hColor hq0 hqsum hqsingle
      hs.le hq.le hr0.le hleft homega (by linarith :
        jointProfileOmega tau ≤ 1) hrho.le hproposal0
      choice OFin hOFin hOpos T decision hdisj hpositive he
    simpa [color, mixedBlockPaletteEquiv] using hsupport.1
  · intro e he v hinc
    have hColor : 0 < Fintype.card (Fin B × Fin k) := by
      simpa using Nat.mul_pos hB hk
    have hs := jointProfile_parameters htau0 htau1
    rcases hs with ⟨hs, _, hq, hr0, homega, homega1,
      hleft, _, hrho, _, _⟩
    have hdisj := G.selectedMixedRelabeledOrdinary_disjoint_tiny
      proposal edgeLabel qLaw R
      (jointProfileRho tau) (jointProfileOmega tau) choice
      bucket (tau / 4) (dyadicSimpleReserveScale (dyadicSimpleRoot n))
      (dyadicSimpleQuantizationScale (dyadicSimpleRoot n)) M
    have hOpos : ∀ o ∈ OFin,
        0 < x o.job ((Fintype.equivFin (Fin B × Fin k)).symm o.color)
          o.leftPlace o.rightPlace := by
      intro o ho
      exact G.selectedDyadicOrdinaryBaseOptionsAny_relabel_mass_pos
        places (dyadicSimpleQuantizationScale (dyadicSimpleRoot n))
        bucket (tau / 4) (dyadicSimpleReserveScale (dyadicSimpleRoot n))
        residual x M o ho
    have hsupport := G.selectedMixedJointColor_support
      proposal edgeLabel qLaw R hColor hq0 hqsum hqsingle
      hs.le hq.le hr0.le hleft homega homega1 hrho.le hproposal0
      choice OFin hOFin hOpos T decision hdisj hpositive he
    have hincLabel := G.decodedMixedGraphLabel_at_inc_of_endpointLabels
      proposal edgeLabel qLaw R choice e _
      ⟨hsupport.2.1, hsupport.2.2⟩ v hinc
    have heq : finProdFinEquiv.symm (color e) =
        (Fintype.equivFin (Fin B × Fin k)).symm (jointColor e) := by
      change finProdFinEquiv.symm
        (mixedBlockPaletteEquiv B k (jointColor e)) = _
      rw [mixedBlockPaletteEquiv_apply, Equiv.symm_apply_apply]
    change G.decodeMixedGraphLabel proposal edgeLabel qLaw R
      v (choice v) (finProdFinEquiv.symm (color e)) = _
    rw [heq]
    exact hincLabel
  · intro v label
    have hsum :
        (∑ c : Fin (B * k),
          if selectedLabel v c = some label then (1 : ℝ) else 0) =
        G.selectedMixedEndpointLabelCount
          proposal edgeLabel qLaw R choice v label := by
      unfold selectedMixedEndpointLabelCount
      exact Equiv.sum_comp finProdFinEquiv.symm
        (fun c : Fin B × Fin k ↦
          if G.decodeMixedGraphLabel proposal edgeLabel qLaw R
            v (choice v) c = some label then (1 : ℝ) else 0)
    have hcard :
        ((Finset.univ.filter (fun c : Fin (B * k) ↦
          selectedLabel v c = some label)).card : ℝ) =
        ∑ c : Fin (B * k),
          if selectedLabel v c = some label then (1 : ℝ) else 0 := by
      simp only [Finset.card_filter, Nat.cast_sum, Nat.cast_ite,
        Nat.cast_one, Nat.cast_zero]
    rw [hcard, hsum]
    exact hlabel v label
  · exact hresidual

end WeightedMultigraph

end
end WeightedEdgeColoring
