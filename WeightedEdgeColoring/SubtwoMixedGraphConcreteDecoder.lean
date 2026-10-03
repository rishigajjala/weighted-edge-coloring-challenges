import WeightedEdgeColoring.SubtwoMixedGraphConcreteSlots

/-!
# The concrete slot and reservoir of a selected mixed atom

The label mixture carries exactly one active local profile.  Its concrete
slots and reservoir obey the local unit-bin inequality, and a positive
paired large option fits the corresponding slot at both physical endpoints.
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

def mixedGraphConcreteSlotSize
    (v : G.V) (c : Color)
    (a : G.MixedGraphAtom proposal edgeLabel qLaw R v c)
    (i : Fin (explicitLargeSlotBound β qstep r)) : ℝ :=
  match a with
  | none => 0
  | some ⟨label, z⟩ =>
      G.localMixedConcreteSlotSize (R v c label) z i

def mixedGraphConcreteReservoirSize
    (v : G.V) (c : Color)
    (a : G.MixedGraphAtom proposal edgeLabel qLaw R v c) : ℝ :=
  match a with
  | none => 0
  | some ⟨label, z⟩ =>
      G.localMixedConcreteReservoirSize (R v c label) z

theorem mixedGraphConcreteSlotSize_nonneg
    (v : G.V) (c : Color)
    (a : G.MixedGraphAtom proposal edgeLabel qLaw R v c)
    (i : Fin (explicitLargeSlotBound β qstep r)) :
    0 ≤ G.mixedGraphConcreteSlotSize proposal edgeLabel qLaw R v c a i := by
  rcases a with _ | ⟨label, z⟩
  · exact le_rfl
  · exact G.localMixedConcreteSlotSize_nonneg (R v c label) z i

theorem mixedGraphConcreteReservoirSize_nonneg
    (v : G.V) (c : Color)
    (a : G.MixedGraphAtom proposal edgeLabel qLaw R v c) :
    0 ≤ G.mixedGraphConcreteReservoirSize
      proposal edgeLabel qLaw R v c a := by
  rcases a with _ | ⟨label, z⟩
  · exact le_rfl
  · exact G.localMixedConcreteReservoirSize_nonneg (R v c label) z

theorem sum_mixedGraphConcreteSlotSize_add_reservoir_le_one
    (v : G.V) (c : Color)
    (a : G.MixedGraphAtom proposal edgeLabel qLaw R v c) :
    (∑ i, G.mixedGraphConcreteSlotSize
      proposal edgeLabel qLaw R v c a i) +
      G.mixedGraphConcreteReservoirSize
        proposal edgeLabel qLaw R v c a ≤ 1 := by
  rcases a with _ | ⟨label, z⟩
  · simp [mixedGraphConcreteSlotSize, mixedGraphConcreteReservoirSize]
  · exact G.sum_localMixedConcreteSlotSize_add_reservoir_le_one
      (R v c label) z

theorem sum_mixedGraphConcreteSlotSize_le_one
    (v : G.V) (c : Color)
    (a : G.MixedGraphAtom proposal edgeLabel qLaw R v c) :
    (∑ i, G.mixedGraphConcreteSlotSize
      proposal edgeLabel qLaw R v c a i) ≤ 1 := by
  have hsafe := G.sum_mixedGraphConcreteSlotSize_add_reservoir_le_one
    proposal edgeLabel qLaw R v c a
  have hres := G.mixedGraphConcreteReservoirSize_nonneg
    proposal edgeLabel qLaw R v c a
  linarith

theorem weight_le_mixedGraphConcreteSlotSize_of_assign_pos
    (hq0 : ∀ v c S, 0 ≤ qLaw v c S)
    (v : G.V) (c : Color) (e : G.StarEdge v)
    (a : G.MixedGraphAtom proposal edgeLabel qLaw R v c)
    (i : Fin (explicitLargeSlotBound β qstep r))
    (hpos : 0 < G.mixedGraphLargeAssign
      proposal edgeLabel qLaw R v c e a i) :
    G.weight e.1 ≤ G.mixedGraphConcreteSlotSize
      proposal edgeLabel qLaw R v c a i := by
  rcases a with _ | ⟨label, z⟩
  · simp [mixedGraphLargeAssign, mixedLabelGraphLargeAssign] at hpos
  · have hfactor : 0 ≤ subsetLabelMass (edgeLabel v) (qLaw v c) label :=
      G.subsetLabelMass_nonneg_local (edgeLabel v) (qLaw v c)
        (hq0 v c) label
    have hlocal0 := G.localExtendedProfileLargeAssign_nonneg
      (R v c label) e z i
    have hlocal : 0 < G.localExtendedProfileLargeAssign
        (R v c label) e z i := by
      have hprod : 0 < subsetLabelMass (edgeLabel v) (qLaw v c) label *
          G.localExtendedProfileLargeAssign (R v c label) e z i := by
        simpa [mixedGraphLargeAssign, mixedLabelGraphLargeAssign] using hpos
      by_contra h
      have hle : G.localExtendedProfileLargeAssign
          (R v c label) e z i ≤ 0 := le_of_not_gt h
      exact (not_lt_of_ge (mul_nonpos_of_nonneg_of_nonpos hfactor hle)) hprod
    exact G.weight_le_localMixedConcreteSlotSize_of_pos
      (R v c label) e z i hlocal

def selectedMixedConcreteSlotSize
    (choice : ∀ v : G.V,
      G.MixedGraphPackedState proposal edgeLabel qLaw R)
    (v : G.V) (c : Color)
    (i : Fin (explicitLargeSlotBound β qstep r)) : ℝ :=
  G.mixedGraphConcreteSlotSize proposal edgeLabel qLaw R v c
    (G.decodeMixedGraphAtom proposal edgeLabel qLaw R v (choice v) c) i

def selectedMixedConcreteReservoirSize
    (choice : ∀ v : G.V,
      G.MixedGraphPackedState proposal edgeLabel qLaw R)
    (v : G.V) (c : Color) : ℝ :=
  G.mixedGraphConcreteReservoirSize proposal edgeLabel qLaw R v c
    (G.decodeMixedGraphAtom proposal edgeLabel qLaw R v (choice v) c)

theorem sum_selectedMixedConcreteSlotSize_add_reservoir_le_one
    (choice : ∀ v : G.V,
      G.MixedGraphPackedState proposal edgeLabel qLaw R)
    (v : G.V) (c : Color) :
    (∑ i, G.selectedMixedConcreteSlotSize
      proposal edgeLabel qLaw R choice v c i) +
      G.selectedMixedConcreteReservoirSize
        proposal edgeLabel qLaw R choice v c ≤ 1 := by
  exact G.sum_mixedGraphConcreteSlotSize_add_reservoir_le_one
    proposal edgeLabel qLaw R v c _

theorem selectedMixedConcreteSlotSize_nonneg
    (choice : ∀ v : G.V,
      G.MixedGraphPackedState proposal edgeLabel qLaw R)
    (v : G.V) (c : Color)
    (i : Fin (explicitLargeSlotBound β qstep r)) :
    0 ≤ G.selectedMixedConcreteSlotSize
      proposal edgeLabel qLaw R choice v c i := by
  exact G.mixedGraphConcreteSlotSize_nonneg
    proposal edgeLabel qLaw R v c _ i

theorem sum_selectedMixedConcreteSlotSize_le_one
    (choice : ∀ v : G.V,
      G.MixedGraphPackedState proposal edgeLabel qLaw R)
    (v : G.V) (c : Color) :
    (∑ i, G.selectedMixedConcreteSlotSize
      proposal edgeLabel qLaw R choice v c i) ≤ 1 := by
  have hsafe := G.sum_selectedMixedConcreteSlotSize_add_reservoir_le_one
    proposal edgeLabel qLaw R choice v c
  have hres := G.mixedGraphConcreteReservoirSize_nonneg
    proposal edgeLabel qLaw R v c
    (G.decodeMixedGraphAtom proposal edgeLabel qLaw R v (choice v) c)
  change 0 ≤ G.selectedMixedConcreteReservoirSize
    proposal edgeLabel qLaw R choice v c at hres
  linarith

theorem weight_le_selectedMixedConcreteSlots_of_large_pos
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
    (hpos : 0 < G.selectedMixedNormalizedLargeOptionMass
      proposal edgeLabel qLaw R rho omega choice e c i j) :
    G.weight e ≤ G.selectedMixedConcreteSlotSize
      proposal edgeLabel qLaw R choice (G.fst e) c i ∧
    G.weight e ≤ G.selectedMixedConcreteSlotSize
      proposal edgeLabel qLaw R choice (G.snd e) c j := by
  let a := G.decodeMixedGraphAtom proposal edgeLabel qLaw R
    (G.fst e) (choice (G.fst e)) c
  let b := G.decodeMixedGraphAtom proposal edgeLabel qLaw R
    (G.snd e) (choice (G.snd e)) c
  have hraw : 0 < G.mixedGraphLargeProductMass
      proposal edgeLabel qLaw R rho omega e c a b i j := by
    exact (G.selectedMixedNormalizedLargeOptionMass_pos_iff
      proposal edgeLabel qLaw R rho omega choice e c i j).mp hpos
  have hy0 : 0 ≤ G.mixedGraphLargeEdgeMass proposal s β e c := by
    unfold mixedGraphLargeEdgeMass
    split
    · exact mul_nonneg hs (hproposal0 e c)
    · exact le_rfl
  have hP := G.smoothedMixedGraphProbability_pos
    proposal edgeLabel qLaw R hq0 hqsum hqsingle
    hs hqstep hr0 hleft homega0 homega1 (G.fst e) c a
  have hQ := G.smoothedMixedGraphProbability_pos
    proposal edgeLabel qLaw R hq0 hqsum hqsingle
    hs hqstep hr0 hleft homega0 homega1 (G.snd e) c b
  have ha0 := G.mixedGraphLargeAssign_nonneg
    proposal edgeLabel qLaw R hq0 (G.fst e) c (G.fstStarEdge e) a i
  have hb0 := G.mixedGraphLargeAssign_nonneg
    proposal edgeLabel qLaw R hq0 (G.snd e) c (G.sndStarEdge e) b j
  have huses := positive_pairedOption_uses rho
    (G.mixedGraphLargeEdgeMass proposal s β e c)
    (G.smoothedMixedGraphProbability proposal edgeLabel qLaw R
      omega (G.fst e) c)
    (G.smoothedMixedGraphProbability proposal edgeLabel qLaw R
      omega (G.snd e) c)
    (fun a i ↦ G.mixedGraphLargeAssign proposal edgeLabel qLaw R
      (G.fst e) c (G.fstStarEdge e) a i)
    (fun b j ↦ G.mixedGraphLargeAssign proposal edgeLabel qLaw R
      (G.snd e) c (G.sndStarEdge e) b j)
    a b i j hrho hy0 hP hQ ha0 hb0
    (by simpa [mixedGraphLargeProductMass] using hraw)
  constructor
  · exact G.weight_le_mixedGraphConcreteSlotSize_of_assign_pos
      proposal edgeLabel qLaw R hq0 (G.fst e) c (G.fstStarEdge e)
      a i huses.1
  · exact G.weight_le_mixedGraphConcreteSlotSize_of_assign_pos
      proposal edgeLabel qLaw R hq0 (G.snd e) c (G.sndStarEdge e)
      b j huses.2

end WeightedMultigraph

end

end WeightedEdgeColoring
