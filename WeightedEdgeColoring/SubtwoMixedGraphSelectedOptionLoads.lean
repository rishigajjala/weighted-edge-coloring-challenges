import WeightedEdgeColoring.SubtwoMixedGraphJointDecoder

/-!
# Actual selected mixed option loads

The candidate rows are additive over source vertices.  This module
transposes those sums to the physical edge options after one packed word
has been selected at every vertex.  Thus the joint selector's capacity
bound applies to the actual large slots and tiny reservoirs.
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

def selectedMixedLargeOptionMass
    (rho omega : ℝ)
    (choice : ∀ v : G.V,
      G.MixedGraphPackedState proposal edgeLabel qLaw R)
    (e : G.E) (c : Color)
    (i j : Fin (explicitLargeSlotBound β qstep r)) : ℝ :=
  G.mixedGraphLargeProductMass proposal edgeLabel qLaw R rho omega e c
    (G.decodeMixedGraphAtom proposal edgeLabel qLaw R
      (G.fst e) (choice (G.fst e)) c)
    (G.decodeMixedGraphAtom proposal edgeLabel qLaw R
      (G.snd e) (choice (G.snd e)) c) i j

def selectedMixedTinyOptionMass
    (rho omega : ℝ)
    (choice : ∀ v : G.V,
      G.MixedGraphPackedState proposal edgeLabel qLaw R)
    (e : G.E) (c : Color) : ℝ :=
  G.mixedGraphTinyProductMass proposal edgeLabel qLaw R rho omega e c
    (G.decodeMixedGraphAtom proposal edgeLabel qLaw R
      (G.fst e) (choice (G.fst e)) c)
    (G.decodeMixedGraphAtom proposal edgeLabel qLaw R
      (G.snd e) (choice (G.snd e)) c)

def selectedMixedLargeSlotLoad
    (rho omega : ℝ)
    (choice : ∀ v : G.V,
      G.MixedGraphPackedState proposal edgeLabel qLaw R)
    (v : G.V) (c : Color)
    (slot : Fin (explicitLargeSlotBound β qstep r)) : ℝ :=
  ∑ e : G.E,
    ((if v = G.fst e then
        ∑ j, G.selectedMixedLargeOptionMass
          proposal edgeLabel qLaw R rho omega choice e c slot j else 0) +
      (if v = G.snd e then
        ∑ i, G.selectedMixedLargeOptionMass
          proposal edgeLabel qLaw R rho omega choice e c i slot else 0))

def selectedMixedTinyReservoirLoad
    (rho omega : ℝ)
    (choice : ∀ v : G.V,
      G.MixedGraphPackedState proposal edgeLabel qLaw R)
    (v : G.V) (c : Color) : ℝ :=
  ∑ e : G.E, if G.Inc v e then
    G.weight e * G.selectedMixedTinyOptionMass
      proposal edgeLabel qLaw R rho omega choice e c else 0

theorem selectedMixedLargeCapacityLoad_eq_slotLoad
    (rho omega : ℝ)
    (choice : ∀ v : G.V,
      G.MixedGraphPackedState proposal edgeLabel qLaw R)
    (v : G.V) (c : Color)
    (slot : Fin (explicitLargeSlotBound β qstep r)) :
    G.selectedMixedCandidateCapacityLoad proposal edgeLabel qLaw R
      rho omega choice c
      (Sum.inl (G.selectedMixedLargeCandidateRow
        proposal edgeLabel qLaw R choice v c slot)) =
    G.selectedMixedLargeSlotLoad proposal edgeLabel qLaw R
      rho omega choice v c slot := by
  classical
  unfold selectedMixedCandidateCapacityLoad mixedCandidateAtomUse
    selectedMixedLargeSlotLoad
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro e _he
  by_cases hfst : v = G.fst e
  · have hsnd : v ≠ G.snd e := by
      intro h
      exact G.noLoop e (hfst.symm.trans h)
    subst v
    have hne : G.fst e ≠ G.snd e := G.noLoop e
    simp [selectedMixedLargeCandidateRow, mixedLargeCandidateEdgeUse,
      selectedMixedLargeOptionMass, hne, hsnd]
  · by_cases hsnd : v = G.snd e
    · subst v
      have hne : G.snd e ≠ G.fst e := (G.noLoop e).symm
      simp [selectedMixedLargeCandidateRow, mixedLargeCandidateEdgeUse,
        selectedMixedLargeOptionMass, hne, hfst]
    · have hfst' : G.fst e ≠ v := Ne.symm hfst
      have hsnd' : G.snd e ≠ v := Ne.symm hsnd
      simp [selectedMixedLargeCandidateRow, mixedLargeCandidateEdgeUse,
        selectedMixedLargeOptionMass,
        hfst, hsnd, hfst', hsnd']

theorem selectedMixedTinyCapacityLoad_eq_reservoirLoad
    (rho omega : ℝ)
    (choice : ∀ v : G.V,
      G.MixedGraphPackedState proposal edgeLabel qLaw R)
    (v : G.V) (c : Color) :
    G.selectedMixedCandidateCapacityLoad proposal edgeLabel qLaw R
      rho omega choice c
      (Sum.inr (G.selectedMixedTinyCandidateRow
        proposal edgeLabel qLaw R choice v c)) =
    G.selectedMixedTinyReservoirLoad proposal edgeLabel qLaw R
      rho omega choice v c := by
  classical
  unfold selectedMixedCandidateCapacityLoad mixedCandidateAtomUse
    selectedMixedTinyReservoirLoad
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro e _he
  by_cases hfst : v = G.fst e
  · have hsnd : v ≠ G.snd e := by
      intro h
      exact G.noLoop e (hfst.symm.trans h)
    subst v
    have hne : G.fst e ≠ G.snd e := G.noLoop e
    simp [selectedMixedTinyCandidateRow, mixedTinyCandidateEdgeUse,
      selectedMixedTinyOptionMass, WeightedMultigraph.Inc, hne, hsnd]
  · by_cases hsnd : v = G.snd e
    · subst v
      have hne : G.snd e ≠ G.fst e := (G.noLoop e).symm
      simp [selectedMixedTinyCandidateRow, mixedTinyCandidateEdgeUse,
        selectedMixedTinyOptionMass, WeightedMultigraph.Inc, hne, hfst]
    · have hfst' : G.fst e ≠ v := Ne.symm hfst
      have hsnd' : G.snd e ≠ v := Ne.symm hsnd
      simp [selectedMixedTinyCandidateRow, mixedTinyCandidateEdgeUse,
        selectedMixedTinyOptionMass, WeightedMultigraph.Inc,
        hfst, hsnd, hfst', hsnd']

theorem selectedMixedLargeSlotLoad_lt
    (rho omega bound : ℝ)
    (choice : ∀ v : G.V,
      G.MixedGraphPackedState proposal edgeLabel qLaw R)
    (v : G.V) (c : Color)
    (slot : Fin (explicitLargeSlotBound β qstep r))
    (hload :
      G.selectedMixedCandidateCapacityLoad proposal edgeLabel qLaw R
        rho omega choice c
        (Sum.inl (G.selectedMixedLargeCandidateRow
          proposal edgeLabel qLaw R choice v c slot)) < bound) :
    G.selectedMixedLargeSlotLoad proposal edgeLabel qLaw R
      rho omega choice v c slot < bound := by
  rw [← G.selectedMixedLargeCapacityLoad_eq_slotLoad
    proposal edgeLabel qLaw R rho omega choice v c slot]
  exact hload

theorem selectedMixedTinyReservoirLoad_lt
    (rho omega bound : ℝ)
    (choice : ∀ v : G.V,
      G.MixedGraphPackedState proposal edgeLabel qLaw R)
    (v : G.V) (c : Color)
    (hload :
      G.selectedMixedCandidateCapacityLoad proposal edgeLabel qLaw R
        rho omega choice c
        (Sum.inr (G.selectedMixedTinyCandidateRow
          proposal edgeLabel qLaw R choice v c)) < bound) :
    G.selectedMixedTinyReservoirLoad proposal edgeLabel qLaw R
      rho omega choice v c < bound := by
  rw [← G.selectedMixedTinyCapacityLoad_eq_reservoirLoad
    proposal edgeLabel qLaw R rho omega choice v c]
  exact hload

theorem positive_selectedMixedLargeOptionMass_endpointLabels
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
    (e : G.E) (c : Color)
    (i j : Fin (explicitLargeSlotBound β qstep r))
    (hpos : 0 < G.selectedMixedLargeOptionMass
      proposal edgeLabel qLaw R rho omega choice e c i j) :
    G.decodeMixedGraphLabel proposal edgeLabel qLaw R
      (G.fst e) (choice (G.fst e)) c =
        some (edgeLabel (G.fst e) (G.fstStarEdge e)) ∧
    G.decodeMixedGraphLabel proposal edgeLabel qLaw R
      (G.snd e) (choice (G.snd e)) c =
        some (edgeLabel (G.snd e) (G.sndStarEdge e)) := by
  exact G.positive_decoded_mixedGraphLargeProductMass_endpointLabels
    proposal edgeLabel qLaw R hq0 hqsum hqsingle
    hs hqstep hr0 hleft homega0 homega1 hrho hproposal0
    e c (choice (G.fst e)) (choice (G.snd e)) i j hpos

theorem positive_selectedMixedTinyOptionMass_endpointLabels
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
    (e : G.E) (c : Color)
    (hpos : 0 < G.selectedMixedTinyOptionMass
      proposal edgeLabel qLaw R rho omega choice e c) :
    G.decodeMixedGraphLabel proposal edgeLabel qLaw R
      (G.fst e) (choice (G.fst e)) c =
        some (edgeLabel (G.fst e) (G.fstStarEdge e)) ∧
    G.decodeMixedGraphLabel proposal edgeLabel qLaw R
      (G.snd e) (choice (G.snd e)) c =
        some (edgeLabel (G.snd e) (G.sndStarEdge e)) := by
  exact G.positive_decoded_mixedGraphTinyProductMass_endpointLabels
    proposal edgeLabel qLaw R hq0 hqsum hqsingle
    hs hqstep hr0 hleft homega0 homega1 hrho hproposal0
    e c (choice (G.fst e)) (choice (G.snd e)) hpos

end WeightedMultigraph

end

end WeightedEdgeColoring
