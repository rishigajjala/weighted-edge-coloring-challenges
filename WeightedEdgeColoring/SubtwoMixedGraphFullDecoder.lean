import WeightedEdgeColoring.SubtwoMixedGraphColorRelabel

/-!
# Combine the actual large-job matching with physical tiny rounding
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

theorem exists_selectedMixedJointPhysicalColor_of_maskedMatching
    (hColor : 0 < Fintype.card Color)
    (hq0 : ∀ v c S, 0 ≤ qLaw v c S)
    (hqsum : ∀ v c, ∑ S, qLaw v c S = 1)
    (hqsingle : ∀ v c S, qLaw v c S ≠ 0 → S ≠ ∅ →
      ∃ label : Label, ∀ f ∈ S, edgeLabel v f = label)
    (hs : 0 ≤ s) (hqstep : 0 ≤ qstep) (hr0 : 0 ≤ r)
    (hleft : 0 ≤ 1 - s * (1 + qstep + r))
    (homega0 : 0 < omega) (homega1 : omega ≤ 1)
    (hrho : 0 ≤ rho) (hproposal0 : ∀ e c, 0 ≤ proposal e c)
    (choice : ∀ v : G.V,
      G.MixedGraphPackedState proposal edgeLabel qLaw R)
    {Class : Type*} [Fintype Class] [DecidableEq Class]
    (bucket : G.E → Class) (gamma : ℝ) (reserve N : ℕ)
    (largeLoss : ℝ) :
    let T := G.selectedMixedTinyEdges (β := β)
    let residual := G.selectedMixedLargeResidual
      proposal edgeLabel qLaw R rho omega choice
    let x := G.selectedMixedNormalizedLargeOptionMass
      proposal edgeLabel qLaw R rho omega choice
    let Hbase := (G.dyadicLargeEdgeOptionSystem
      (Color := Color) (explicitLargeSlotBound β qstep r)
      bucket gamma reserve residual).quantized N
        (G.dyadicLargeEdgeMass (explicitLargeSlotBound β qstep r)
          bucket gamma reserve residual x)
    (∃ (M : Finset (QuantizedCopy N
        (G.dyadicLargeEdgeMass (explicitLargeSlotBound β qstep r)
          bucket gamma reserve residual x))),
      Hbase.IsPartialMatching M ∧
      ∀ v, G.uncoveredLargeStarWeight Hbase β M v ≤ largeLoss) →
    ∃ (M : Finset (QuantizedCopy N
        (G.dyadicLargeEdgeMass (explicitLargeSlotBound β qstep r)
          bucket gamma reserve residual x)))
      (hM : Hbase.IsPartialMatching M),
      (∀ v, G.uncoveredLargeStarWeight Hbase β M v ≤ largeLoss) ∧
      let O := G.selectedDyadicOrdinaryBaseOptionsAny
        (explicitLargeSlotBound β qstep r) N bucket gamma reserve residual x M
      let OFin := O.map
        (OrdinarySlotChoice.colorEquiv (Fintype.equivFin Color)).toEmbedding
      let hO := G.selectedDyadicOrdinaryBaseOptionsAny_isPartialMatching
        (explicitLargeSlotBound β qstep r) N bucket gamma reserve residual x M hM
      let hOFin := ordinarySlotChoice_colorEquiv_isPartialMatching
        G.fst G.snd (explicitLargeSlotBound β qstep r)
        (Fintype.equivFin Color) O hO
      ∃ decision : {e : G.E // e ∈ T} →
          Option (Fin (Fintype.card Color)),
        (∀ v d,
          G.colorLoadOn
            (G.ordinarySelectedEdges OFin ∪
              G.tinyDecisionColoredEdges T decision)
            (G.ordinaryTinyJointColor hColor OFin hOFin T decision) v d ≤
            (∑ i, G.encodedSelectedMixedConcreteSlotSize
              proposal edgeLabel qLaw R choice v d i) +
            G.selectedMixedNormalizedTinyReservoirLoad
              proposal edgeLabel qLaw R rho omega choice v
                ((Fintype.equivFin Color).symm d) + 2 * β) ∧
        ∀ v,
          G.tinyResidualIntegralLossLoad decision v ≤
            G.tinyResidualLossLoad T
              (fun e ↦ G.selectedMixedResidualOptionMass
                proposal edgeLabel qLaw R rho omega choice e.1) v + 2 * β := by
  dsimp only
  intro hmatching
  rcases hmatching with ⟨M, hM, hlargeLoss⟩
  refine ⟨M, hM, hlargeLoss, ?_⟩
  exact G.exists_selectedMixedAnyJointPhysicalColor
    proposal edgeLabel qLaw R hColor hq0 hqsum hqsingle
    hs hqstep hr0 hleft homega0 homega1 hrho hproposal0
    choice bucket gamma reserve N
    (G.selectedMixedLargeResidual
      proposal edgeLabel qLaw R rho omega choice) M hM

/-- The selected normalized mixed state has one physical assignment whose
large-job loss is controlled by the closed matching iteration and whose tiny
load and loss are controlled by reservoir rounding. -/
theorem exists_selectedMixedJointPhysicalColor_of_maskedClosedScalars
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
    (homega0 : 0 < omega) (homega1 : omega ≤ 1)
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
      N C S0 lambda L K steps) :
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
      (∀ v, G.uncoveredLargeStarWeight Hbase β M v ≤
        (1 - (1 - delta) * variableSlackA alpha gamma lambda / 8) ^ steps * n +
          (((L + 1) * (K - 1) : ℕ) : ℝ)) ∧
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
        (∀ v d,
          G.colorLoadOn
            (G.ordinarySelectedEdges OFin ∪
              G.tinyDecisionColoredEdges T decision)
            (G.ordinaryTinyJointColor hColor OFin hOFin T decision) v d ≤
            (∑ i, G.encodedSelectedMixedConcreteSlotSize
              proposal edgeLabel qLaw R choice v d i) +
            G.selectedMixedNormalizedTinyReservoirLoad
              proposal edgeLabel qLaw R rho omega choice v
                ((Fintype.equivFin Color).symm d) + 2 * β) ∧
        ∀ v,
          G.tinyResidualIntegralLossLoad decision v ≤
            G.tinyResidualLossLoad T
              (fun e ↦ G.selectedMixedResidualOptionMass
                proposal edgeLabel qLaw R rho omega choice e.1) v + 2 * β := by
  dsimp only
  have hmatching := G.exists_selectedMixedMaskedLargePartialMatching
    proposal edgeLabel qLaw R hmult hn hN hq0 hqmarg hqsingle hqsum
    hs hqstep hr0 hleft homega0 homega1 hrho hC0 hproposal0 hproposal
    choice bucket hstar hcapacity hordinaryCap hreserve
    hextraGamma0 hextraGamma1 hextraCap hordinaryCodegree hordinaryPair
    hextraCodegree hpairCodegree hCN hNC hE hchoiceCap numeric
  exact G.exists_selectedMixedJointPhysicalColor_of_maskedMatching
    proposal edgeLabel qLaw R hColor hq0 hqsum hqsingle
    hs hqstep hr0 hleft homega0 homega1 hrho hproposal0 choice
    bucket extraGamma reserve N _ hmatching

end WeightedMultigraph

end

end WeightedEdgeColoring
