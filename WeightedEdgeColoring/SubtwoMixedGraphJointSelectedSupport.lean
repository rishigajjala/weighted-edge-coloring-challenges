import WeightedEdgeColoring.SubtwoMixedGraphJointColorSupport

/-! Physical support and both endpoint labels for each selected joint color. -/

namespace WeightedEdgeColoring
open scoped BigOperators
noncomputable section
namespace WeightedMultigraph
universe u
variable (G : WeightedMultigraph.{u})
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

/-- Every relabeled ordinary option extracted from a quantized matching has
positive selected mass in the original color coordinates. -/
theorem selectedDyadicOrdinaryBaseOptionsAny_relabel_mass_pos
    {Class : Type*} [Fintype Class] [DecidableEq Class]
    (K N : ℕ) (bucket : G.E → Class) (gamma : ℝ) (reserve : ℕ)
    (residual : G.E → ℝ)
    (x : G.E → Color → Fin K → Fin K → ℝ)
    (M : Finset (QuantizedCopy N
      (G.dyadicLargeEdgeMass K bucket gamma reserve residual x)))
    (o : OrdinarySlotChoice G.E (Fin (Fintype.card Color)) K)
    (ho : o ∈ (G.selectedDyadicOrdinaryBaseOptionsAny
      K N bucket gamma reserve residual x M).map
        (OrdinarySlotChoice.colorEquiv
          (Fintype.equivFin Color)).toEmbedding) :
    0 < x o.job ((Fintype.equivFin Color).symm o.color)
      o.leftPlace o.rightPlace := by
  obtain ⟨o0,ho0,rfl⟩ := Finset.mem_map.mp ho
  simpa [OrdinarySlotChoice.colorEquiv] using
    G.selectedDyadicOrdinaryBaseOptionsAny_mass_pos
      K N bucket gamma reserve residual x M ho0

/-- A selected ordinary edge retains positive proposal support and the two
labels in the selected packed words. -/
theorem selectedMixedOrdinaryJointColor_support
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
    (O : Finset (OrdinarySlotChoice G.E
      (Fin (Fintype.card Color)) (explicitLargeSlotBound β qstep r)))
    (hO : (OrdinarySlotChoice.system G.fst G.snd
      (explicitLargeSlotBound β qstep r)).IsPartialMatching O)
    (hOpos : ∀ o ∈ O,
      0 < G.selectedMixedNormalizedLargeOptionMass
        proposal edgeLabel qLaw R rho omega choice o.job
          ((Fintype.equivFin Color).symm o.color) o.leftPlace o.rightPlace)
    (T : Finset G.E)
    (decision : {e : G.E // e ∈ T} → Option (Fin (Fintype.card Color)))
    {e : G.E} (he : e ∈ G.ordinarySelectedEdges O) :
    let c := (Fintype.equivFin Color).symm
      (G.ordinaryTinyJointColor hColor O hO T decision e)
    0 < proposal e c ∧
      G.decodeMixedGraphLabel proposal edgeLabel qLaw R
        (G.fst e) (choice (G.fst e)) c =
          some (edgeLabel (G.fst e) (G.fstStarEdge e)) ∧
      G.decodeMixedGraphLabel proposal edgeLabel qLaw R
        (G.snd e) (choice (G.snd e)) c =
          some (edgeLabel (G.snd e) (G.sndStarEdge e)) := by
  dsimp only
  obtain ⟨o,ho,hjob,hcolor⟩ :=
    G.ordinaryTinyJointColor_selectedOption hColor O hO T decision he
  have hmass := hOpos o ho
  rw [hjob, ←hcolor] at hmass
  exact ⟨G.positive_selectedMixedNormalizedLargeOptionMass_proposal
      proposal edgeLabel qLaw R hs hproposal0 rho omega choice e
      ((Fintype.equivFin Color).symm
        (G.ordinaryTinyJointColor hColor O hO T decision e))
      o.leftPlace o.rightPlace hmass,
    G.positive_selectedMixedNormalizedLargeOptionMass_endpointLabels
      proposal edgeLabel qLaw R hq0 hqsum hqsingle hs hqstep hr0
      hleft homega0 homega1 hrho hproposal0 choice e
      ((Fintype.equivFin Color).symm
        (G.ordinaryTinyJointColor hColor O hO T decision e))
      o.leftPlace o.rightPlace hmass⟩

/-- The same conclusion for an integrally selected tiny edge. -/
theorem selectedMixedTinyJointColor_support
    (hColor : 0 < Fintype.card Color)
    (hs : 0 ≤ s) (hproposal0 : ∀ e c, 0 ≤ proposal e c)
    (rho omega : ℝ)
    (choice : ∀ v : G.V,
      G.MixedGraphPackedState proposal edgeLabel qLaw R)
    (O : Finset (OrdinarySlotChoice G.E
      (Fin (Fintype.card Color)) (explicitLargeSlotBound β qstep r)))
    (hO : (OrdinarySlotChoice.system G.fst G.snd
      (explicitLargeSlotBound β qstep r)).IsPartialMatching O)
    (T : Finset G.E)
    (decision : {e : G.E // e ∈ T} → Option (Fin (Fintype.card Color)))
    (hdisj : Disjoint (G.ordinarySelectedEdges O) T)
    (hpositive : ∀ e d, decision e = some d →
      0 < G.selectedMixedNormalizedTinyOptionMass
        proposal edgeLabel qLaw R rho omega choice e.1
          ((Fintype.equivFin Color).symm d) ∧
      G.decodeMixedGraphLabel proposal edgeLabel qLaw R
        (G.fst e.1) (choice (G.fst e.1))
          ((Fintype.equivFin Color).symm d) =
        some (edgeLabel (G.fst e.1) (G.fstStarEdge e.1)) ∧
      G.decodeMixedGraphLabel proposal edgeLabel qLaw R
        (G.snd e.1) (choice (G.snd e.1))
          ((Fintype.equivFin Color).symm d) =
        some (edgeLabel (G.snd e.1) (G.sndStarEdge e.1)))
    {e : G.E} (he : e ∈ G.tinyDecisionColoredEdges T decision) :
    let c := (Fintype.equivFin Color).symm
      (G.ordinaryTinyJointColor hColor O hO T decision e)
    0 < proposal e c ∧
      G.decodeMixedGraphLabel proposal edgeLabel qLaw R
        (G.fst e) (choice (G.fst e)) c =
          some (edgeLabel (G.fst e) (G.fstStarEdge e)) ∧
      G.decodeMixedGraphLabel proposal edgeLabel qLaw R
        (G.snd e) (choice (G.snd e)) c =
          some (edgeLabel (G.snd e) (G.sndStarEdge e)) := by
  dsimp only
  obtain ⟨hT,hdecision⟩ :=
    G.ordinaryTinyJointColor_tinyDecision hColor O hO T decision hdisj he
  have hp := hpositive ⟨e,hT⟩
    (G.ordinaryTinyJointColor hColor O hO T decision e) hdecision
  exact ⟨G.positive_selectedMixedNormalizedTinyOptionMass_proposal
      proposal edgeLabel qLaw R hs hproposal0 rho omega choice e _ hp.1,
    hp.2⟩

/-- Both branches of the actual joint decoder preserve positive proposal
support and the endpoint label selected by its packed word. -/
theorem selectedMixedJointColor_support
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
    (O : Finset (OrdinarySlotChoice G.E
      (Fin (Fintype.card Color)) (explicitLargeSlotBound β qstep r)))
    (hO : (OrdinarySlotChoice.system G.fst G.snd
      (explicitLargeSlotBound β qstep r)).IsPartialMatching O)
    (hOpos : ∀ o ∈ O,
      0 < G.selectedMixedNormalizedLargeOptionMass
        proposal edgeLabel qLaw R rho omega choice o.job
          ((Fintype.equivFin Color).symm o.color) o.leftPlace o.rightPlace)
    (T : Finset G.E)
    (decision : {e : G.E // e ∈ T} → Option (Fin (Fintype.card Color)))
    (hdisj : Disjoint (G.ordinarySelectedEdges O) T)
    (hpositive : ∀ e d, decision e = some d →
      0 < G.selectedMixedNormalizedTinyOptionMass
        proposal edgeLabel qLaw R rho omega choice e.1
          ((Fintype.equivFin Color).symm d) ∧
      G.decodeMixedGraphLabel proposal edgeLabel qLaw R
        (G.fst e.1) (choice (G.fst e.1))
          ((Fintype.equivFin Color).symm d) =
        some (edgeLabel (G.fst e.1) (G.fstStarEdge e.1)) ∧
      G.decodeMixedGraphLabel proposal edgeLabel qLaw R
        (G.snd e.1) (choice (G.snd e.1))
          ((Fintype.equivFin Color).symm d) =
        some (edgeLabel (G.snd e.1) (G.sndStarEdge e.1)))
    {e : G.E}
    (he : e ∈ G.ordinarySelectedEdges O ∪
      G.tinyDecisionColoredEdges T decision) :
    let c := (Fintype.equivFin Color).symm
      (G.ordinaryTinyJointColor hColor O hO T decision e)
    0 < proposal e c ∧
      G.decodeMixedGraphLabel proposal edgeLabel qLaw R
        (G.fst e) (choice (G.fst e)) c =
          some (edgeLabel (G.fst e) (G.fstStarEdge e)) ∧
      G.decodeMixedGraphLabel proposal edgeLabel qLaw R
        (G.snd e) (choice (G.snd e)) c =
          some (edgeLabel (G.snd e) (G.sndStarEdge e)) := by
  rcases Finset.mem_union.mp he with heOrd | heTiny
  · exact G.selectedMixedOrdinaryJointColor_support
      proposal edgeLabel qLaw R hColor hq0 hqsum hqsingle
      hs hqstep hr0 hleft homega0 homega1 hrho hproposal0
      choice O hO hOpos T decision heOrd
  · exact G.selectedMixedTinyJointColor_support
      proposal edgeLabel qLaw R hColor hs hproposal0 rho omega
      choice O hO T decision hdisj hpositive heTiny

/-- The endpoint-label pair can be used at either incidence orientation. -/
theorem decodedMixedGraphLabel_at_inc_of_endpointLabels
    (choice : ∀ v : G.V,
      G.MixedGraphPackedState proposal edgeLabel qLaw R)
    (e : G.E) (c : Color)
    (hlabels :
      G.decodeMixedGraphLabel proposal edgeLabel qLaw R
        (G.fst e) (choice (G.fst e)) c =
          some (edgeLabel (G.fst e) (G.fstStarEdge e)) ∧
      G.decodeMixedGraphLabel proposal edgeLabel qLaw R
        (G.snd e) (choice (G.snd e)) c =
          some (edgeLabel (G.snd e) (G.sndStarEdge e)))
    (v : G.V) (hv : G.Inc v e) :
    G.decodeMixedGraphLabel proposal edgeLabel qLaw R v (choice v) c =
      some (edgeLabel v ⟨e,hv⟩) := by
  rcases hv with hfst | hsnd
  · subst v
    simpa using hlabels.1
  · subst v
    simpa using hlabels.2

end WeightedMultigraph
end
end WeightedEdgeColoring
