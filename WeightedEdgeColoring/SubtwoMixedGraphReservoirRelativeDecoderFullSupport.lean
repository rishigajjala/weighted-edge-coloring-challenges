import WeightedEdgeColoring.SubtwoMixedGraphReservoirRelativeDecoder

/-!
# Support-preserving feasible decoder using the reservoir-relative selector row
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

theorem exists_selectedMixedAnyJointPhysicalColor_feasible_of_relative_support
    (hColor : 0 < Fintype.card Color)
    (hq0 : ∀ w c S, 0 ≤ qLaw w c S)
    (hqsum : ∀ w c, ∑ S, qLaw w c S = 1)
    (hqsingle : ∀ w c S, qLaw w c S ≠ 0 → S ≠ ∅ →
      ∃ label : Label, ∀ f ∈ S, edgeLabel w f = label)
    (hs : 0 ≤ s) (hqstep : 0 ≤ qstep) (hr0 : 0 ≤ r)
    (hleft : 0 ≤ 1 - s * (1 + qstep + r))
    (homega0 : 0 < omega) (homega1 : omega ≤ 1)
    (hrho : 0 ≤ rho) (hproposal0 : ∀ e c, 0 ≤ proposal e c)
    (choice : ∀ w : G.V,
      G.MixedGraphPackedState proposal edgeLabel qLaw RG)
    (hr1 : r ≤ 1) (rate deviation : ℝ) (hrate1 : rate ≤ 1)
    (hmargin : deviation + 2 * β ≤ (1 - rate) * r)
    (hRelative : ∀ w c,
      G.selectedMixedNormalizedTinyReservoirLoad
        proposal edgeLabel qLaw RG rho omega choice w c <
      rate * G.selectedMixedConcreteReservoirSize
        proposal edgeLabel qLaw RG choice w c + deviation)
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
      (∀ e d, decision e = some d →
        0 < G.selectedMixedNormalizedTinyOptionMass
          proposal edgeLabel qLaw RG rho omega choice e.1
            ((Fintype.equivFin Color).symm d) ∧
        G.decodeMixedGraphLabel proposal edgeLabel qLaw RG
          (G.fst e.1) (choice (G.fst e.1))
            ((Fintype.equivFin Color).symm d) =
          some (edgeLabel (G.fst e.1) (G.fstStarEdge e.1)) ∧
        G.decodeMixedGraphLabel proposal edgeLabel qLaw RG
          (G.snd e.1) (choice (G.snd e.1))
            ((Fintype.equivFin Color).symm d) =
          some (edgeLabel (G.snd e.1) (G.sndStarEdge e.1))) ∧
      G.IsFeasibleOn
        (G.ordinarySelectedEdges OFin ∪ G.tinyDecisionColoredEdges T decision)
        (G.ordinaryTinyJointColor hColor OFin hOFin T decision) ∧
      ∀ w,
        G.tinyResidualIntegralLossLoad decision w ≤
          G.tinyResidualLossLoad T
            (fun e ↦ G.selectedMixedResidualOptionMass
              proposal edgeLabel qLaw RG rho omega choice e.1) w + 2 * β := by
  classical
  obtain ⟨decision, hpositive, _hresidual, htiny, hloss⟩ :=
    G.exists_selectedMixedTinyColorDecision
      proposal edgeLabel qLaw RG hq0 hqsum hqsingle hs hqstep hr0
      hleft homega0 homega1 hrho hproposal0 choice
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
  have hdisj : Disjoint (G.ordinarySelectedEdges OFin) T := by
    rw [Finset.disjoint_left]
    intro e heOrd heTiny
    rcases (G.mem_ordinarySelectedEdges_iff OFin e).mp heOrd with
      ⟨oFin, hoFin, rfl⟩
    rcases Finset.mem_map.mp hoFin with ⟨o, ho, rfl⟩
    have hpos := G.selectedDyadicOrdinaryBaseOptionsAny_mass_pos
      (explicitLargeSlotBound β qstep r) N bucket gamma reserve residual
      x M ho
    have hzero := G.selectedMixedNormalizedLargeOptionMass_eq_zero_of_tiny
      proposal edgeLabel qLaw RG rho omega choice o.job o.color
      o.leftPlace o.rightPlace (G.mem_selectedMixedTinyEdges.mp heTiny)
    exact (ne_of_gt hpos) hzero
  refine ⟨decision, hpositive, ?_, hloss⟩
  intro w d
  rw [G.colorLoadOn_ordinaryTinyJoint_eq hColor OFin hOFin T decision hdisj w d]
  have hlarge := G.selectedMixedAnyMatching_load_le_concreteSlotSum
    proposal edgeLabel qLaw RG hq0 hqsum hqsingle hs hqstep hr0
    hleft homega0 homega1 hrho hproposal0 choice
    bucket gamma reserve N residual M hM w d
  let c := (Fintype.equivFin Color).symm d
  have hsafe := G.sum_selectedMixedConcreteSlotSize_add_reservoir_le_one
    proposal edgeLabel qLaw RG choice w c
  have hsafe' :
      (∑ i, G.encodedSelectedMixedConcreteSlotSize
        proposal edgeLabel qLaw RG choice w d i) +
      G.selectedMixedConcreteReservoirSize proposal edgeLabel qLaw RG
        choice w c ≤ 1 := by
    simpa [encodedSelectedMixedConcreteSlotSize, c] using hsafe
  rcases G.selectedMixedConcreteReservoirSize_zero_or_ge_r
    proposal edgeLabel qLaw RG hr1 choice w c with hzero | hreserve
  · have htinyZero :=
      G.selectedMixedIntegralTinyColorLoad_eq_zero_of_reservoir_zero
        proposal edgeLabel qLaw RG rho omega choice decision
        (fun e d hed ↦ (hpositive e d hed).1) w d hzero
    rw [htinyZero]
    rw [hzero] at hsafe'
    linarith
  · have htinyBound := htiny w c
    have hcolor : (Fintype.equivFin Color) c = d :=
      Equiv.apply_symm_apply _ _
    rw [hcolor] at htinyBound
    have hrelative := hRelative w c
    have hgap : (1 - rate) * r ≤
        (1 - rate) * G.selectedMixedConcreteReservoirSize
          proposal edgeLabel qLaw RG choice w c :=
      mul_le_mul_of_nonneg_left hreserve (sub_nonneg.mpr hrate1)
    linarith


end WeightedMultigraph

end

end WeightedEdgeColoring
