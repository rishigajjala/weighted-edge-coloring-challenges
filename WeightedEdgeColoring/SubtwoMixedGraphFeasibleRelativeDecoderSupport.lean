import WeightedEdgeColoring.SubtwoMixedGraphReservoirSelectedDecoder
import WeightedEdgeColoring.SubtwoMixedGraphWholePhysicalLoss
import WeightedEdgeColoring.SubtwoMixedGraphReservoirRelativeDecoder
import WeightedEdgeColoring.SubtwoMixedGraphWholePhysicalLossSupport

/-!
# One-call feasible physical decoder from a relative tiny-reservoir bound
-/

namespace WeightedEdgeColoring

open scoped BigOperators

noncomputable section

namespace WeightedMultigraph

variable (G : WeightedMultigraph)
variable {Color Label : Type*} [Fintype Color] [DecidableEq Color]
  [Fintype Label] [DecidableEq Label]
variable (proposal : G.E → Color → ℝ)
variable (edgeLabel : ∀ v : G.V, G.StarEdge v → Label)
variable (qLaw : ∀ v : G.V, Color → Finset (G.StarEdge v) → ℝ)
variable {s β qstep r : ℝ} {hβ : 0 < β} {hr : 0 < r}
variable (R : ∀ v c label,
  G.BoundedProfileRealization
    (G.conditionalEndpointProposal (edgeLabel v)
      (fun e : G.StarEdge v ↦ proposal e.1 c) (qLaw v c) label)
    s β qstep r hβ hr)

theorem exists_selectedMixedFeasibleFullDecoder_of_relativeScalars_support
    {n N reserve C E S0 steps L K lambda mult : ℕ}
    {rho omega C0 extraGamma bound alpha gamma delta : ℝ}
    (hColor : 0 < Fintype.card Color)
    (hmult : G.PairMultiplicityAtMost mult)
    (hn : 0 < n) (hN : 0 < N)
    (hq0 : ∀ v c S, 0 ≤ qLaw v c S)
    (hqmarg : ∀ v c (f : G.StarEdge v),
      (∑ S, if f ∈ S then qLaw v c S else 0) = proposal f.1 c)
    (hqsingle : ∀ v c S, qLaw v c S ≠ 0 → S ≠ ∅ →
      ∃ label : Label, ∀ f ∈ S, edgeLabel v f = label)
    (hqsum : ∀ v c, ∑ S, qLaw v c S = 1)
    (hs : 0 ≤ s) (hqstep : 0 ≤ qstep) (hr0 : 0 ≤ r)
    (hleft : 0 ≤ 1 - s * (1 + qstep + r))
    (homega0 : 0 < omega) (homega1 : omega < 1)
    (hrho : 0 ≤ rho) (hC0 : 0 ≤ C0)
    (hproposal0 : ∀ e c, 0 ≤ proposal e c)
    (hproposal : ∀ e c, proposal e c ≤ C0 / (n : ℝ))
    (choice : ∀ v : G.V,
      G.MixedGraphPackedState proposal edgeLabel qLaw R)
    {Class : Type*} [Fintype Class] [DecidableEq Class]
    (bucket : G.E → Class)
    (hstar : ∀ v, G.starWeight v ≤ n)
    (hcapacity : ∀ v c place,
      G.selectedMixedCandidateCapacityLoad
        proposal edgeLabel qLaw R rho omega choice c
          (Sum.inl (G.selectedMixedLargeCandidateRow
            proposal edgeLabel qLaw R choice v c place)) < bound)
    (hordinaryCap : (N : ℝ) * bound ≤ S0)
    (hreserve : 0 < reserve)
    (hextraGamma0 : 0 ≤ extraGamma)
    (hextraGamma1 : extraGamma < 1)
    (hextraCap : (1 - extraGamma) * N ≤ S0)
    (hordinaryCodegree : (N : ℝ) *
      ((explicitLargeSlotBound β qstep r : ℝ) *
        mixedGraphCandidateCapacityScale (Label := Label)
          (β := β) (qstep := qstep) (r := r) rho s omega C0 /
          (n : ℝ)) ≤ lambda)
    (hordinaryPair : mixedGraphCandidateCapacityScale (Label := Label)
      (β := β) (qstep := qstep) (r := r) rho s omega C0 / n ≤
        1 / (reserve : ℝ))
    (hextraCodegree : (N : ℝ) / reserve ≤ lambda)
    (hpairCodegree : (mult : ℝ) * N / reserve ≤ lambda)
    (hCN : C ≤ N) (hNC : 0 < N - C)
    (hE : 2 * ((n : ℝ) / β / (1 - extraGamma) +
      1 + reserve) ≤ E)
    (hchoiceCap : Fintype.card Color * explicitLargeSlotBound β qstep r *
      explicitLargeSlotBound β qstep r + E ≤ C)
    (numeric : MixedMaskedClosedScalars β alpha gamma delta
      N C S0 lambda L K steps)
    (scale deviation ratio : ℝ) (hscale : 0 < scale)
    (hr1 : r ≤ 1) (hrate1 : rho / (1 - omega) ≤ 1)
    (hmargin : scale / (n : ℝ) * deviation + 2 * β ≤
      (1 - rho / (1 - omega)) * r)
    (hRelative : ∀ v c,
      G.selectedMixedNormalizedTinyReservoirLoad
        proposal edgeLabel qLaw R rho omega choice v c <
      rho / (1 - omega) *
        G.selectedMixedConcreteReservoirSize
          proposal edgeLabel qLaw R choice v c +
      scale / (n : ℝ) * deviation)
    (upper : Class → ℝ) (hupper0 : ∀ h, 0 ≤ upper h)
    (hweightUpper : ∀ e, G.weight e ≤ upper (bucket e))
    (hratioUpper : ∀ e,
      0 < G.selectedMixedLargeResidual
        proposal edgeLabel qLaw R rho omega choice e →
      upper (bucket e) ≤ ratio * G.weight e) :
    let T := G.selectedMixedTinyEdges (β := β)
    let residual := G.selectedMixedLargeResidual
      proposal edgeLabel qLaw R rho omega choice
    let x := G.selectedMixedNormalizedLargeOptionMass
      proposal edgeLabel qLaw R rho omega choice
    let Hbase := (G.dyadicLargeEdgeOptionSystem
      (Color := Color) (explicitLargeSlotBound β qstep r)
      bucket extraGamma reserve residual).quantized N
        (G.dyadicLargeEdgeMass (explicitLargeSlotBound β qstep r)
          bucket extraGamma reserve residual x)
    ∃ (M : Finset (QuantizedCopy N
        (G.dyadicLargeEdgeMass (explicitLargeSlotBound β qstep r)
          bucket extraGamma reserve residual x)))
      (hM : Hbase.IsPartialMatching M),
      let O := G.selectedDyadicOrdinaryBaseOptionsAny
        (explicitLargeSlotBound β qstep r) N bucket extraGamma reserve residual x M
      let OFin := O.map
        (OrdinarySlotChoice.colorEquiv (Fintype.equivFin Color)).toEmbedding
      let hO := G.selectedDyadicOrdinaryBaseOptionsAny_isPartialMatching
        (explicitLargeSlotBound β qstep r) N bucket extraGamma reserve residual x M hM
      let hOFin := ordinarySlotChoice_colorEquiv_isPartialMatching
        G.fst G.snd (explicitLargeSlotBound β qstep r)
        (Fintype.equivFin Color) O hO
      ∃ decision : {e : G.E // e ∈ T} →
          Option (Fin (Fintype.card Color)),
        G.IsFeasibleOn
          (G.ordinarySelectedEdges OFin ∪ G.tinyDecisionColoredEdges T decision)
          (G.ordinaryTinyJointColor hColor OFin hOFin T decision) ∧
        ∀ v,
          (∑ e ∈ Finset.univ \ (G.ordinarySelectedEdges OFin ∪
            G.tinyDecisionColoredEdges T decision),
              if G.Inc v e then G.weight e else 0) ≤
            (1 - (1 - delta) * variableSlackA alpha gamma lambda / 8) ^ steps * n +
              (((L + 1) * (K - 1) : ℕ) : ℝ) +
              2 * ratio * G.weightedResidualStar residual v / (1 - extraGamma) +
              2 * (1 + (reserve : ℝ)) * (∑ h, upper h) +
              G.tinyResidualLossLoad T
                (fun e ↦ G.selectedMixedResidualOptionMass
                  proposal edgeLabel qLaw R rho omega choice e.1) v + 2 * β := by
  dsimp only
  obtain ⟨M, hM, hlarge⟩ :=
    G.exists_selectedMixedMaskedLargePartialMatching
      proposal edgeLabel qLaw R hmult hn hN hq0 hqmarg hqsingle hqsum
      hs hqstep hr0 hleft homega0 homega1.le hrho hC0 hproposal0 hproposal
      choice bucket hstar hcapacity hordinaryCap hreserve
      hextraGamma0 hextraGamma1 hextraCap hordinaryCodegree hordinaryPair
      hextraCodegree hpairCodegree hCN hNC hE hchoiceCap numeric
  obtain ⟨decision, hfeasible, htiny⟩ :=
    G.exists_selectedMixedAnyJointPhysicalColor_feasible_of_relative
      proposal edgeLabel qLaw R hColor hq0 hqsum hqsingle
      hs hqstep hr0 hleft homega0 homega1.le hrho hproposal0 choice
      hr1 (rho / (1 - omega)) (scale / (n : ℝ) * deviation)
      hrate1 hmargin hRelative bucket extraGamma reserve N
      (G.selectedMixedLargeResidual proposal edgeLabel qLaw R
        rho omega choice) M hM
  refine ⟨M, hM, decision, hfeasible, ?_⟩
  intro v
  have hdisjoint := G.selectedMixedRelabeledOrdinary_disjoint_tiny
    proposal edgeLabel qLaw R rho omega choice bucket extraGamma reserve N M
  have hT : ∀ e, e ∈ G.selectedMixedTinyEdges (β := β) ↔
      G.weight e < β := fun e ↦ G.mem_selectedMixedTinyEdges
  have hresidual0 := G.selectedMixedLargeResidual_nonneg
    proposal edgeLabel qLaw R rho omega choice
  have hwhole := G.uncolored_selectedMixed_joint_starWeight_le_of_support
    (explicitLargeSlotBound β qstep r) N β bucket extraGamma ratio reserve
    (G.selectedMixedLargeResidual proposal edgeLabel qLaw R
      rho omega choice)
    (G.selectedMixedNormalizedLargeOptionMass proposal edgeLabel qLaw R
      rho omega choice)
    M hM (G.selectedMixedTinyEdges (β := β)) hT decision hdisjoint
    hresidual0 hreserve hextraGamma1 upper hupper0 hweightUpper hratioUpper
    (fun _ ↦ (1 - (1 - delta) * variableSlackA alpha gamma lambda / 8) ^ steps * n +
      (((L + 1) * (K - 1) : ℕ) : ℝ))
    (fun w ↦ G.tinyResidualLossLoad (G.selectedMixedTinyEdges (β := β))
      (fun e ↦ G.selectedMixedResidualOptionMass
        proposal edgeLabel qLaw R rho omega choice e.1) w + 2 * β)
    hlarge htiny v
  simpa only [add_assoc] using hwhole

end WeightedMultigraph

end

end WeightedEdgeColoring
