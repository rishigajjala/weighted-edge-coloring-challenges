import WeightedEdgeColoring.SubtwoMixedGraphBlockUniformThreshold

/-! The numerical threshold is chosen before the graph and its proposal. -/

namespace WeightedEdgeColoring

open scoped BigOperators

noncomputable section

namespace WeightedMultigraph

theorem mixedGraph_eventually_uniformPhysicalDecoder
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
    let scale := (mult : ℝ) * A
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
    let residualRate := 4 * tau + epsMix + t +
      D * (A * (jointProfileRho tau * jointProfileS tau)) /
        (4 * t) + eta
    ∃ selected : ∀ v : G.V, ∀ c : Fin B × Fin k,
        G.MixedGraphAtom proposal edgeLabel qLaw R v c,
      let choice : ∀ v : G.V,
          G.MixedGraphPackedState proposal edgeLabel qLaw R :=
        fun v ↦ G.encodeMixedGraphWord proposal edgeLabel qLaw R
          v (selected v)
      (∀ v label,
        G.selectedMixedEndpointLabelCount
          proposal edgeLabel qLaw R choice v label <
        (∑ c : Fin B × Fin k,
          subsetLabelMass (edgeLabel v) (qLaw v c) label) +
        ((B : ℝ) * k) * tau + eta * n) ∧
      let residual := G.selectedMixedLargeResidual
        proposal edgeLabel qLaw R
        (jointProfileRho tau) (jointProfileOmega tau) choice
      let x := G.selectedMixedNormalizedLargeOptionMass
        proposal edgeLabel qLaw R
        (jointProfileRho tau) (jointProfileOmega tau) choice
      let bucket := dyadicBucket (jointProfileBeta tau) Lbucket G.weight
      let Hbase := (G.dyadicLargeEdgeOptionSystem
        (explicitLargeSlotBound (jointProfileBeta tau)
          (jointProfileQ tau) (jointProfileR tau))
        bucket (tau / 4) reserve residual).quantized N
          (G.dyadicLargeEdgeMass
            (explicitLargeSlotBound (jointProfileBeta tau)
              (jointProfileQ tau) (jointProfileR tau))
            bucket (tau / 4) reserve residual x)
      ∃ (M : Finset (QuantizedCopy N
          (G.dyadicLargeEdgeMass
            (explicitLargeSlotBound (jointProfileBeta tau)
              (jointProfileQ tau) (jointProfileR tau))
            bucket (tau / 4) reserve residual x)))
        (hM : Hbase.IsPartialMatching M),
        let O := G.selectedDyadicOrdinaryBaseOptionsAny
          (explicitLargeSlotBound (jointProfileBeta tau)
            (jointProfileQ tau) (jointProfileR tau))
          N bucket (tau / 4) reserve residual x M
        let OFin := O.map
          (OrdinarySlotChoice.colorEquiv
            (Fintype.equivFin (Fin B × Fin k))).toEmbedding
        let hO := G.selectedDyadicOrdinaryBaseOptionsAny_isPartialMatching
          (explicitLargeSlotBound (jointProfileBeta tau)
            (jointProfileQ tau) (jointProfileR tau))
          N bucket (tau / 4) reserve residual x M hM
        let hOFin := ordinarySlotChoice_colorEquiv_isPartialMatching
          G.fst G.snd (explicitLargeSlotBound (jointProfileBeta tau)
            (jointProfileQ tau) (jointProfileR tau))
          (Fintype.equivFin (Fin B × Fin k)) O hO
        ∃ decision : {e : G.E //
            e ∈ G.selectedMixedTinyEdges (β := jointProfileBeta tau)} →
            Option (Fin (Fintype.card (Fin B × Fin k))),
          (∀ e d, decision e = some d →
            0 < G.selectedMixedNormalizedTinyOptionMass
              proposal edgeLabel qLaw R
              (jointProfileRho tau) (jointProfileOmega tau) choice e.1
              ((Fintype.equivFin (Fin B × Fin k)).symm d) ∧
            G.decodeMixedGraphLabel proposal edgeLabel qLaw R
              (G.fst e.1) (choice (G.fst e.1))
                ((Fintype.equivFin (Fin B × Fin k)).symm d) =
              some (edgeLabel (G.fst e.1) (G.fstStarEdge e.1)) ∧
            G.decodeMixedGraphLabel proposal edgeLabel qLaw R
              (G.snd e.1) (choice (G.snd e.1))
                ((Fintype.equivFin (Fin B × Fin k)).symm d) =
              some (edgeLabel (G.snd e.1) (G.sndStarEdge e.1))) ∧
          let colored := G.ordinarySelectedEdges OFin ∪
            G.tinyDecisionColoredEdges
              (G.selectedMixedTinyEdges (β := jointProfileBeta tau))
              decision
          let color := G.ordinaryTinyJointColor
            (by simpa using Nat.mul_pos hB hk)
            OFin hOFin
            (G.selectedMixedTinyEdges (β := jointProfileBeta tau))
            decision
          G.IsFeasibleOn colored color ∧
          ∀ v,
            (∑ e ∈ Finset.univ \ colored,
              if G.Inc v e then G.weight e else 0) ≤
            traceEps * n + (((L + 1) * (K - 1) : ℕ) : ℝ) +
              (4 / (1 - tau / 4) + 1) * (residualRate * n) +
              8 * (1 + (reserve : ℝ)) +
              2 * jointProfileBeta tau := by
  obtain ⟨n0, hnum⟩ := mixedGraph_eventually_uniformPhysicalNumerics
    (Label := Label) (k := k) (mult := mult) (Lbucket := Lbucket)
    (tau := tau) (C0 := C0) (t := t) (eta := eta)
    (alpha := alpha) (delta := delta) (traceEps := traceEps)
    hk hmult0 htau0 htau1 hC0 ht heta hdyadicCover
    halpha halphaSmall halphaDelta hdelta0 hdelta1 hdeltaHalf
    htraceEps0 htraceEps1
  refine ⟨max 1 n0, ?_⟩
  intro n B hn hpalette G proposal edgeLabel qLaw hβ hr R
  dsimp only
  intro hmult hB hq0 hqmarg hqsingle hqsum hproposal0
    hproposal hmass hdeficit hstar
  have hn0 : n0 ≤ n := (le_max_right 1 n0).trans hn
  have hnPos : 0 < n := by
    have h1 : 1 ≤ n := (le_max_left 1 n0).trans hn
    omega
  have hnums := hnum n B hn0 hpalette
  dsimp only at hnums
  rcases hnums with ⟨numeric, htrace, hscalar, hCN, hloss,
    hN, hreserve, hcodeg, hpair, hextraCodeg, hpairCodeg, hE, hchoice⟩
  exact G.exists_uniformPhysicalMixedBlockDecoder
    proposal edgeLabel qLaw R htau0 htau1 hmult0 hmult
    hnPos hB hk hq0 hqmarg hqsingle hqsum hC0 ht hepsMix
    hproposal0 hproposal hmass hdeficit hstar hscalar
    hN hreserve hCN hloss rfl hcodeg hpair hextraCodeg
    hpairCodeg hE hchoice numeric htrace
    hdyadicCover hdyadicTop

end WeightedMultigraph

end
end WeightedEdgeColoring
