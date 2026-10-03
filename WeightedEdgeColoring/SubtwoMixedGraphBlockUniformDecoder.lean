import WeightedEdgeColoring.SubtwoMixedGraphBlockPhysicalAssembly
import WeightedEdgeColoring.SubtwoMixedGraphDyadicBucketPhysical
import WeightedEdgeColoring.SubtwoMixedGraphJointInitialSlotBudget
import WeightedEdgeColoring.SubtwoMixedGraphFeasibleRelativeDecoderFullSupport

/-! One physical mixed-block application.  The numerical premises are
graph-independent and are supplied eventually by the dyadic scalar lemmas. -/

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
variable {tau : ℝ} {hβ : 0 < jointProfileBeta tau}
  {hr : 0 < jointProfileR tau}
variable (R : ∀ v c label,
  G.BoundedProfileRealization
    (G.conditionalEndpointProposal (edgeLabel v)
      (fun e : G.StarEdge v ↦ proposal e.1 c) (qLaw v c) label)
    (jointProfileS tau) (jointProfileBeta tau)
      (jointProfileQ tau) (jointProfileR tau) hβ hr)

theorem exists_uniformPhysicalMixedBlockDecoder
    {n N reserve C E S0 steps L K lambda mult : ℕ}
    {C0 D t eta epsMix alpha delta traceEps : ℝ}
    (htau0 : 0 < tau) (htau1 : tau ≤ 1 / 4)
    (hL : 0 < mult) (hmult : G.PairMultiplicityAtMost mult)
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
    (hscalar : jointProfileUniformScalarEvent Label B k mult n
      tau C0 D t eta)
    (hN : 0 < N) (hreserve : 0 < reserve)
    (hCN : C ≤ N)
    (hloss : (C : ℝ) + 1 ≤ (tau / 8) * N)
    (hS0 : S0 =
      RankThreeOptionSystem.OriginalIterationState.fixedSlackPaddedSlotTarget
        (tau / 8) (N - C))
    (hordinaryCodegree : (N : ℝ) *
      ((explicitLargeSlotBound (jointProfileBeta tau)
        (jointProfileQ tau) (jointProfileR tau) : ℝ) *
        mixedGraphCandidateCapacityScale (Label := Label)
          (β := jointProfileBeta tau) (qstep := jointProfileQ tau)
          (r := jointProfileR tau)
          (jointProfileRho tau) (jointProfileS tau)
          (jointProfileOmega tau) C0 / (n : ℝ)) ≤ lambda)
    (hordinaryPair :
      mixedGraphCandidateCapacityScale (Label := Label)
        (β := jointProfileBeta tau) (qstep := jointProfileQ tau)
        (r := jointProfileR tau)
        (jointProfileRho tau) (jointProfileS tau)
        (jointProfileOmega tau) C0 / n ≤
          1 / (reserve : ℝ))
    (hextraCodegree : (N : ℝ) / reserve ≤ lambda)
    (hpairCodegree : (mult : ℝ) * N / reserve ≤ lambda)
    (hE : 2 * ((n : ℝ) / jointProfileBeta tau /
      (1 - tau / 4) + 1 + reserve) ≤ E)
    (hchoiceCap :
      B * k *
        explicitLargeSlotBound (jointProfileBeta tau)
          (jointProfileQ tau) (jointProfileR tau) *
        explicitLargeSlotBound (jointProfileBeta tau)
          (jointProfileQ tau) (jointProfileR tau) + E ≤ C)
    (numeric : MixedMaskedClosedScalars
      (jointProfileBeta tau) alpha (tau / 8) delta
      N C S0 lambda L K steps)
    (htrace : (1 - (1 - delta) *
      variableSlackA alpha (tau / 8) lambda / 8) ^
        steps ≤ traceEps)
    {Lbucket : ℕ}
    (hcover : 1 ≤ dyadicScale (jointProfileBeta tau) Lbucket)
    (htop : dyadicScale (jointProfileBeta tau) Lbucket < 2) :
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
  classical
  rcases jointProfile_parameters htau0 htau1 with
    ⟨hs, hbeta, hq, hrpos, homega0, _, hleft, hr1, hrho, _, _⟩
  have homega1 : jointProfileOmega tau < 1 := by
    unfold jointProfileOmega
    linarith
  have hβ1 : jointProfileBeta tau ≤ 1 := by
    unfold jointProfileBeta
    nlinarith [sq_nonneg tau]
  have hextra0 : (0 : ℝ) ≤ tau / 4 := by positivity
  have hextra1 : tau / 4 < 1 := by linarith
  have hrate1 :
      jointProfileRho tau / (1 - jointProfileOmega tau) ≤ 1 := by
    unfold jointProfileRho jointProfileOmega
    apply (div_le_one (by linarith : 0 < 1 - tau)).2
    linarith
  dsimp only at hscalar ⊢
  have hscalar' := hscalar
  dsimp only [jointProfileUniformScalarEvent] at hscalar'
  rcases hscalar' with ⟨hdev, _hrate, hmargin, _hlabelError, _hvariance⟩
  obtain ⟨selected, hcap, hrelative, hlabel, hresidual⟩ :=
    G.exists_fullMixedWord_jointProfile_uniform
      proposal edgeLabel qLaw R htau0 htau1 hL hmult
      hn hB hk hq0 hqmarg hqsingle hqsum
      hC0 ht heps hproposal0 hproposal hmass hdeficit hstar hscalar
  let choice : ∀ v : G.V,
      G.MixedGraphPackedState proposal edgeLabel qLaw R :=
    fun v ↦ G.encodeMixedGraphWord proposal edgeLabel qLaw R v (selected v)
  refine ⟨selected, hlabel, ?_⟩
  have hslots := jointProfile_selected_initialSlotCaps
    htau0 htau1 hCN hloss hdev
  rw [← hS0] at hslots
  rcases hslots with ⟨hordinaryCap0, hextraCap0, _⟩
  have hordinaryCap1 : (N : ℝ) * (1 - tau / 2) ≤ S0 := by
    calc
      _ ≤ (N : ℝ) * (1 - tau / 4) :=
        mul_le_mul_of_nonneg_left (by linarith only [htau0])
          (Nat.cast_nonneg N)
      _ ≤ S0 := by simpa only [mul_comm] using hextraCap0
  have hNC : 0 < N - C := by
    have hgamma : tau / 8 ≤ 1 := by linarith only [htau1]
    have hN0 : (0 : ℝ) ≤ N := Nat.cast_nonneg N
    have hmul : (tau / 8) * (N : ℝ) ≤ N := by
      simpa using mul_le_mul_of_nonneg_right hgamma hN0
    have hC1 : (C : ℝ) + 1 ≤ N := hloss.trans hmul
    have hltR : (C : ℝ) < N := by
      linarith only [hC1]
    have hlt : C < N := by exact_mod_cast hltR
    exact Nat.sub_pos_of_lt hlt
  have hscale : 0 <
      (mult : ℝ) *
        mixedCandidateOrientedScale (Label := Label)
          (β := jointProfileBeta tau) (qstep := jointProfileQ tau)
          (r := jointProfileR tau)
          (jointProfileRho tau) (jointProfileS tau)
          (jointProfileOmega tau) C0 := by
    apply mul_pos (by exact_mod_cast hL)
    exact mixedCandidateOrientedScale_pos hrho hs homega0 hC0
  have hcard : 0 < Fintype.card (Fin B × Fin k) := by
    simpa using Nat.mul_pos hB hk
  have hchoiceCap' :
      Fintype.card (Fin B × Fin k) *
        explicitLargeSlotBound (jointProfileBeta tau)
          (jointProfileQ tau) (jointProfileR tau) *
        explicitLargeSlotBound (jointProfileBeta tau)
          (jointProfileQ tau) (jointProfileR tau) + E ≤ C := by
    simpa using hchoiceCap
  have hbucket := G.selectedMixedLargeResidual_dyadicBucket_data_of_cover
    proposal edgeLabel qLaw R hβ1 Lbucket hcover htop
    (jointProfileRho tau) (jointProfileOmega tau) choice
  rcases hbucket with ⟨hweightUpper, hratioUpper, hsumUpper⟩
  have hcapacity : ∀ v c place,
      G.selectedMixedCandidateCapacityLoad
        proposal edgeLabel qLaw R
        (jointProfileRho tau) (jointProfileOmega tau) choice c
          (Sum.inl (G.selectedMixedLargeCandidateRow
            proposal edgeLabel qLaw R choice v c place)) <
        1 - tau / 2 := by
    intro v c place
    exact hcap c (Sum.inl (G.selectedMixedLargeCandidateRow
      proposal edgeLabel qLaw R choice v c place))
  let A := mixedCandidateOrientedScale (Label := Label)
    (β := jointProfileBeta tau) (qstep := jointProfileQ tau)
    (r := jointProfileR tau) (jointProfileRho tau)
    (jointProfileS tau) (jointProfileOmega tau) C0
  let scale : ℝ := (mult : ℝ) * A
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
  obtain ⟨M, hM, decision, hpositive, hfeasible, hbound⟩ :=
    G.exists_selectedMixedFeasibleFullDecoder_of_relativeScalars_fullSupport
      proposal edgeLabel qLaw R hcard hmult hn hN
      hq0 hqmarg hqsingle hqsum hs.le hq.le hrpos.le hleft
      homega0 homega1
      hrho.le hC0.le hproposal0 hproposal choice
      (dyadicBucket (jointProfileBeta tau) Lbucket G.weight)
      hstar hcapacity hordinaryCap1 hreserve hextra0 hextra1
      hextraCap0 hordinaryCodegree hordinaryPair
      hextraCodegree hpairCodegree hCN hNC hE hchoiceCap' numeric
      scale deviation (2 : ℝ) hscale hr1 hrate1 hmargin hrelative
      (dyadicUpper (jointProfileBeta tau))
      (dyadicUpper_nonneg hbeta.le)
      hweightUpper hratioUpper
  refine ⟨M, hM, decision, hpositive, hfeasible, ?_⟩
  intro v
  have hlarge := G.weightedSelectedMixedLargeResidual_le_fullStar
    proposal edgeLabel qLaw R
      (jointProfileRho tau) (jointProfileOmega tau) choice v
  have htiny := G.tinyResidualLossLoad_selectedMixed_le_fullStar
    proposal edgeLabel qLaw R
      (jointProfileRho tau) (jointProfileOmega tau) choice v
  let residualRate : ℝ := 4 * tau + epsMix + t +
    D * (A * (jointProfileRho tau * jointProfileS tau)) /
      (4 * t) + eta
  have hR : G.weightedResidualStar
      (G.selectedMixedResidualOptionMass proposal edgeLabel qLaw R
        (jointProfileRho tau) (jointProfileOmega tau) choice) v ≤
      residualRate * n := hresidual v
  have hdenom : (0 : ℝ) < 1 - tau / 4 := by linarith
  have hlarge' : 4 *
      G.weightedResidualStar
        (G.selectedMixedLargeResidual proposal edgeLabel qLaw R
          (jointProfileRho tau) (jointProfileOmega tau) choice) v /
        (1 - tau / 4) ≤
      (4 / (1 - tau / 4)) * (residualRate * n) := by
    have hmul := mul_le_mul_of_nonneg_left
      (hlarge.trans hR) (by norm_num : (0 : ℝ) ≤ 4)
    calc
      _ ≤ 4 * (residualRate * n) / (1 - tau / 4) :=
        div_le_div_of_nonneg_right hmul hdenom.le
      _ = _ := by ring
  have htrace' := mul_le_mul_of_nonneg_right htrace
    (Nat.cast_nonneg n : (0 : ℝ) ≤ n)
  have hupper' := mul_le_mul_of_nonneg_left hsumUpper
    (by positivity : (0 : ℝ) ≤ 2 * (1 + (reserve : ℝ)))
  have hv := hbound v
  nlinarith only [hv, hlarge', htrace', hupper', htiny.trans hR]

end WeightedMultigraph

end
end WeightedEdgeColoring
