import WeightedEdgeColoring.SubtwoMixedGraphLargeMatchingDecoder

/-!
# One physical colouring from large matching and tiny decisions

The ordinary matching and the tiny decisions concern disjoint physical
edges.  Their joint colouring uses the same finite palette.  The exact
load identity gives a concrete row bound from the selected slot sizes and
the selected tiny reservoir load, and the tiny residual decision gives an
endpoint loss bound.
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

theorem exists_selectedMixedJointPhysicalColor
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
    (residual : G.E → ℝ)
    (M : Finset (QuantizedCopy N
      (G.dyadicLargeEdgeMass (explicitLargeSlotBound β qstep r)
        bucket gamma reserve residual
        (G.encodedSelectedMixedNormalizedLarge
          proposal edgeLabel qLaw R rho omega choice))))
    (hM : ((G.dyadicLargeEdgeOptionSystem
        (explicitLargeSlotBound β qstep r)
        bucket gamma reserve residual).quantized N
      (G.dyadicLargeEdgeMass (explicitLargeSlotBound β qstep r)
        bucket gamma reserve residual
        (G.encodedSelectedMixedNormalizedLarge
          proposal edgeLabel qLaw R rho omega choice))).IsPartialMatching M) :
    let T := G.selectedMixedTinyEdges (β := β)
    let O := G.selectedDyadicOrdinaryBaseOptions
      (Fintype.card Color) (explicitLargeSlotBound β qstep r) N
      bucket gamma reserve residual
      (G.encodedSelectedMixedNormalizedLarge
        proposal edgeLabel qLaw R rho omega choice) M
    let hO := G.selectedDyadicOrdinaryBaseOptions_isPartialMatching
      (Fintype.card Color) (explicitLargeSlotBound β qstep r) N
      bucket gamma reserve residual
      (G.encodedSelectedMixedNormalizedLarge
        proposal edgeLabel qLaw R rho omega choice) M hM
    ∃ decision : {e : G.E // e ∈ T} →
        Option (Fin (Fintype.card Color)),
      (∀ v d,
        G.colorLoadOn
          (G.ordinarySelectedEdges O ∪ G.tinyDecisionColoredEdges T decision)
          (G.ordinaryTinyJointColor hColor O hO T decision) v d ≤
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
  classical
  obtain ⟨decision, _hpositive, _hresidual, htiny, hloss⟩ :=
    G.exists_selectedMixedTinyColorDecision
      proposal edgeLabel qLaw R hq0 hqsum hqsingle hs hqstep hr0
      hleft homega0 homega1 hrho hproposal0 choice
  let T := G.selectedMixedTinyEdges (β := β)
  let x := G.encodedSelectedMixedNormalizedLarge
    proposal edgeLabel qLaw R rho omega choice
  let O := G.selectedDyadicOrdinaryBaseOptions
    (Fintype.card Color) (explicitLargeSlotBound β qstep r) N
    bucket gamma reserve residual x M
  let hO := G.selectedDyadicOrdinaryBaseOptions_isPartialMatching
    (Fintype.card Color) (explicitLargeSlotBound β qstep r) N
    bucket gamma reserve residual x M hM
  have hdisj : Disjoint (G.ordinarySelectedEdges O) T :=
    G.selectedMixedLargeMatching_disjoint_tinyEdges
      proposal edgeLabel qLaw R rho omega choice bucket gamma reserve
      N residual M
  refine ⟨decision, ?_, hloss⟩
  intro v d
  rw [G.colorLoadOn_ordinaryTinyJoint_eq hColor O hO T decision hdisj v d]
  have hlarge := G.selectedMixedLargeMatching_load_le_concreteSlotSum
    proposal edgeLabel qLaw R hq0 hqsum hqsingle hs hqstep hr0
    hleft homega0 homega1 hrho hproposal0 choice
    bucket gamma reserve N residual M hM v d
  have htiny' := htiny v ((Fintype.equivFin Color).symm d)
  have hcolor : (Fintype.equivFin Color)
      ((Fintype.equivFin Color).symm d) = d :=
    Equiv.apply_symm_apply _ _
  rw [hcolor] at htiny'
  dsimp only [O, hO] at hlarge ⊢
  linarith

end WeightedMultigraph

end

end WeightedEdgeColoring
