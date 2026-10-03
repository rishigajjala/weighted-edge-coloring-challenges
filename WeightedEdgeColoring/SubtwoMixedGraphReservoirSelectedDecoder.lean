import WeightedEdgeColoring.SubtwoMixedGraphReservoirRelativeDecoder

/-!
# Exact feasible decoder using the reservoir-relative selector row
-/

namespace WeightedEdgeColoring

open scoped BigOperators

noncomputable section

namespace WeightedMultigraph

variable (G : WeightedMultigraph)
variable {Color Label : Type*} [Fintype Color] [DecidableEq Color]
  [Fintype Label] [DecidableEq Label]
variable (proposal : G.E → Color → ℝ)
variable (edgeLabel : ∀ w : G.V, G.StarEdge w → Label)
variable (qLaw : ∀ w : G.V, Color → Finset (G.StarEdge w) → ℝ)
variable {s β qstep r : ℝ} {hβ : 0 < β} {hr : 0 < r}
variable (RG : ∀ w c label,
  G.BoundedProfileRealization
    (G.conditionalEndpointProposal (edgeLabel w)
      (fun e : G.StarEdge w ↦ proposal e.1 c) (qLaw w c) label)
    s β qstep r hβ hr)

theorem exists_selectedMixedAnyJointPhysicalColor_feasible_of_jointRows
    {n : ℕ} (hn : 0 < n)
    (hColor : 0 < Fintype.card Color)
    (scale deviation : ℝ) (hscale : 0 < scale)
    (hq0 : ∀ w c S, 0 ≤ qLaw w c S)
    (hqmarg : ∀ w c (f : G.StarEdge w),
      (∑ S, if f ∈ S then qLaw w c S else 0) = proposal f.1 c)
    (hqsum : ∀ w c, ∑ S, qLaw w c S = 1)
    (hqsingle : ∀ w c S, qLaw w c S ≠ 0 → S ≠ ∅ →
      ∃ label : Label, ∀ f ∈ S, edgeLabel w f = label)
    (hs : 0 ≤ s) (hqstep : 0 ≤ qstep) (hr0 : 0 ≤ r)
    (hleft : 0 ≤ 1 - s * (1 + qstep + r))
    (homega0 : 0 < omega) (homega1 : omega < 1)
    (hrho : 0 ≤ rho) (hproposal0 : ∀ e c, 0 ≤ proposal e c)
    (choice : ∀ w : G.V,
      G.MixedGraphPackedState proposal edgeLabel qLaw RG)
    (hr1 : r ≤ 1)
    (hrate1 : rho / (1 - omega) ≤ 1)
    (hmargin : scale / (n : ℝ) * deviation + 2 * β ≤
      (1 - rho / (1 - omega)) * r)
    (hRows : ∀ row :
      (Σ c : Color, G.MixedCandidateRowAt proposal edgeLabel qLaw RG c) ⊕
        (G.V × Option Label),
      FiniteCategoricalSelection.rowLoad
        (G.mixedGraphJointUse proposal edgeLabel qLaw RG
          hColor n scale rho omega) row choice <
      FiniteCategoricalSelection.rowMean
        (G.paddedMixedGraphWordProbability
          proposal edgeLabel qLaw RG omega)
        (G.mixedGraphJointUse proposal edgeLabel qLaw RG
          hColor n scale rho omega) row + deviation)
    {Class : Type*} [Fintype Class] [DecidableEq Class]
    (bucket : G.E → Class) (gamma : ℝ) (reserve N : ℕ)
    (residual : G.E → ℝ)
    (M : Finset (QuantizedCopy N
      (G.dyadicLargeEdgeMass (explicitLargeSlotBound β qstep r)
        bucket gamma reserve residual
        (G.selectedMixedNormalizedLargeOptionMass
          proposal edgeLabel qLaw RG rho omega choice))))
    (hM : ((G.dyadicLargeEdgeOptionSystem
      (Color := Color) (explicitLargeSlotBound β qstep r)
      bucket gamma reserve residual).quantized N
        (G.dyadicLargeEdgeMass (explicitLargeSlotBound β qstep r)
          bucket gamma reserve residual
          (G.selectedMixedNormalizedLargeOptionMass
            proposal edgeLabel qLaw RG rho omega choice))).IsPartialMatching M) :
    let T := G.selectedMixedTinyEdges (β := β)
    let x := G.selectedMixedNormalizedLargeOptionMass
      proposal edgeLabel qLaw RG rho omega choice
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
      G.IsFeasibleOn
        (G.ordinarySelectedEdges OFin ∪ G.tinyDecisionColoredEdges T decision)
        (G.ordinaryTinyJointColor hColor OFin hOFin T decision) ∧
      ∀ w,
        G.tinyResidualIntegralLossLoad decision w ≤
          G.tinyResidualLossLoad T
            (fun e ↦ G.selectedMixedResidualOptionMass
              proposal edgeLabel qLaw RG rho omega choice e.1) w + 2 * β := by
  have hRelative : ∀ w c,
      G.selectedMixedNormalizedTinyReservoirLoad
        proposal edgeLabel qLaw RG rho omega choice w c <
      rho / (1 - omega) *
        G.selectedMixedConcreteReservoirSize
          proposal edgeLabel qLaw RG choice w c +
        scale / (n : ℝ) * deviation := by
    intro w c
    exact G.selectedMixedNormalizedTinyReservoirLoad_lt_relative
      proposal edgeLabel qLaw RG hn hColor scale rho omega deviation hscale
      hq0 hqmarg hqsingle hqsum hs hqstep hr0 hleft
      homega0 homega1 hrho hproposal0 choice w c
      (hRows (Sum.inl ⟨c, Sum.inr
        (G.selectedMixedTinyCandidateRow
          proposal edgeLabel qLaw RG choice w c)⟩))
  exact G.exists_selectedMixedAnyJointPhysicalColor_feasible_of_relative
    proposal edgeLabel qLaw RG hColor hq0 hqsum hqsingle
    hs hqstep hr0 hleft homega0 homega1.le hrho hproposal0 choice
    hr1 (rho / (1 - omega)) (scale / (n : ℝ) * deviation)
    hrate1 hmargin hRelative bucket gamma reserve N residual M hM

end WeightedMultigraph

end

end WeightedEdgeColoring
