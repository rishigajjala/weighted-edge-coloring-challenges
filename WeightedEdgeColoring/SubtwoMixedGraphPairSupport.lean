import WeightedEdgeColoring.SubtwoMixedGraphLabelSupport

/-!
# Both endpoint labels survive matched mixed options

Positive paired-option mass uses positive local assignment at each endpoint.
The assigned edge therefore has the label selected by that endpoint's
decoded mixed atom.  This remains true when the two endpoint labels differ.
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

theorem positive_mixedGraphLargeProductMass_endpointLabels
    (hq0 : ∀ v c S, 0 ≤ qLaw v c S)
    (hqsum : ∀ v c, ∑ S, qLaw v c S = 1)
    (hqsingle : ∀ v c S, qLaw v c S ≠ 0 → S ≠ ∅ →
      ∃ label : Label, ∀ e ∈ S, edgeLabel v e = label)
    (hs : 0 ≤ s) (hqstep : 0 ≤ qstep) (hr0 : 0 ≤ r)
    (hleft : 0 ≤ 1 - s * (1 + qstep + r))
    (homega0 : 0 < omega) (homega1 : omega ≤ 1)
    (hrho : 0 ≤ rho) (hproposal0 : ∀ e c, 0 ≤ proposal e c)
    (e : G.E) (c : Color)
    (a : G.MixedGraphAtom proposal edgeLabel qLaw R (G.fst e) c)
    (b : G.MixedGraphAtom proposal edgeLabel qLaw R (G.snd e) c)
    (i j : Fin (explicitLargeSlotBound β qstep r))
    (hpos : 0 < G.mixedGraphLargeProductMass proposal edgeLabel qLaw R
      rho omega e c a b i j) :
    G.mixedGraphAtomLabel proposal edgeLabel qLaw R (G.fst e) c a =
      some (edgeLabel (G.fst e) (G.fstStarEdge e)) ∧
    G.mixedGraphAtomLabel proposal edgeLabel qLaw R (G.snd e) c b =
      some (edgeLabel (G.snd e) (G.sndStarEdge e)) := by
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
    proposal edgeLabel qLaw R hq0 (G.fst e) c
    (G.fstStarEdge e) a i
  have hb0 := G.mixedGraphLargeAssign_nonneg
    proposal edgeLabel qLaw R hq0 (G.snd e) c
    (G.sndStarEdge e) b j
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
    (by simpa [mixedGraphLargeProductMass] using hpos)
  constructor
  · exact G.positive_mixedLabelGraphLargeAssign_label
      (edgeLabel (G.fst e))
      (fun f : G.StarEdge (G.fst e) ↦ proposal f.1 c)
      (qLaw (G.fst e) c) (R (G.fst e) c)
      (hq0 (G.fst e) c) hs (G.fstStarEdge e) a i huses.1
  · exact G.positive_mixedLabelGraphLargeAssign_label
      (edgeLabel (G.snd e))
      (fun f : G.StarEdge (G.snd e) ↦ proposal f.1 c)
      (qLaw (G.snd e) c) (R (G.snd e) c)
      (hq0 (G.snd e) c) hs (G.sndStarEdge e) b j huses.2

theorem positive_mixedGraphTinyProductMass_endpointLabels
    (hq0 : ∀ v c S, 0 ≤ qLaw v c S)
    (hqsum : ∀ v c, ∑ S, qLaw v c S = 1)
    (hqsingle : ∀ v c S, qLaw v c S ≠ 0 → S ≠ ∅ →
      ∃ label : Label, ∀ e ∈ S, edgeLabel v e = label)
    (hs : 0 ≤ s) (hqstep : 0 ≤ qstep) (hr0 : 0 ≤ r)
    (hleft : 0 ≤ 1 - s * (1 + qstep + r))
    (homega0 : 0 < omega) (homega1 : omega ≤ 1)
    (hrho : 0 ≤ rho) (hproposal0 : ∀ e c, 0 ≤ proposal e c)
    (e : G.E) (c : Color)
    (a : G.MixedGraphAtom proposal edgeLabel qLaw R (G.fst e) c)
    (b : G.MixedGraphAtom proposal edgeLabel qLaw R (G.snd e) c)
    (hpos : 0 < G.mixedGraphTinyProductMass proposal edgeLabel qLaw R
      rho omega e c a b) :
    G.mixedGraphAtomLabel proposal edgeLabel qLaw R (G.fst e) c a =
      some (edgeLabel (G.fst e) (G.fstStarEdge e)) ∧
    G.mixedGraphAtomLabel proposal edgeLabel qLaw R (G.snd e) c b =
      some (edgeLabel (G.snd e) (G.sndStarEdge e)) := by
  have hy0 : 0 ≤ G.mixedGraphTinyEdgeMass proposal s β e c := by
    unfold mixedGraphTinyEdgeMass
    split
    · exact mul_nonneg hs (hproposal0 e c)
    · exact le_rfl
  have hP := G.smoothedMixedGraphProbability_pos
    proposal edgeLabel qLaw R hq0 hqsum hqsingle
    hs hqstep hr0 hleft homega0 homega1 (G.fst e) c a
  have hQ := G.smoothedMixedGraphProbability_pos
    proposal edgeLabel qLaw R hq0 hqsum hqsingle
    hs hqstep hr0 hleft homega0 homega1 (G.snd e) c b
  have ha0 := G.mixedGraphTinyAssign_nonneg
    proposal edgeLabel qLaw R hq0 (G.fst e) c
    (G.fstStarEdge e) a
  have hb0 := G.mixedGraphTinyAssign_nonneg
    proposal edgeLabel qLaw R hq0 (G.snd e) c
    (G.sndStarEdge e) b
  have huses := positive_pairedOption_uses rho
    (G.mixedGraphTinyEdgeMass proposal s β e c)
    (G.smoothedMixedGraphProbability proposal edgeLabel qLaw R
      omega (G.fst e) c)
    (G.smoothedMixedGraphProbability proposal edgeLabel qLaw R
      omega (G.snd e) c)
    (fun a (_ : Fin 1) ↦ G.mixedGraphTinyAssign proposal edgeLabel qLaw R
      (G.fst e) c (G.fstStarEdge e) a)
    (fun b (_ : Fin 1) ↦ G.mixedGraphTinyAssign proposal edgeLabel qLaw R
      (G.snd e) c (G.sndStarEdge e) b)
    a b 0 0 hrho hy0 hP hQ ha0 hb0
    (by simpa [mixedGraphTinyProductMass] using hpos)
  constructor
  · exact G.positive_mixedLabelGraphTinyAssign_label
      (edgeLabel (G.fst e))
      (fun f : G.StarEdge (G.fst e) ↦ proposal f.1 c)
      (qLaw (G.fst e) c) (R (G.fst e) c)
      (hq0 (G.fst e) c) hs (G.fstStarEdge e) a huses.1
  · exact G.positive_mixedLabelGraphTinyAssign_label
      (edgeLabel (G.snd e))
      (fun f : G.StarEdge (G.snd e) ↦ proposal f.1 c)
      (qLaw (G.snd e) c) (R (G.snd e) c)
      (hq0 (G.snd e) c) hs (G.sndStarEdge e) b huses.2

/-- A selected packed pair can use a large edge only when its decoded
endpoint labels agree with that physical edge. -/
theorem positive_decoded_mixedGraphLargeProductMass_endpointLabels
    (hq0 : ∀ v c S, 0 ≤ qLaw v c S)
    (hqsum : ∀ v c, ∑ S, qLaw v c S = 1)
    (hqsingle : ∀ v c S, qLaw v c S ≠ 0 → S ≠ ∅ →
      ∃ label : Label, ∀ f ∈ S, edgeLabel v f = label)
    (hs : 0 ≤ s) (hqstep : 0 ≤ qstep) (hr0 : 0 ≤ r)
    (hleft : 0 ≤ 1 - s * (1 + qstep + r))
    (homega0 : 0 < omega) (homega1 : omega ≤ 1)
    (hrho : 0 ≤ rho) (hproposal0 : ∀ e c, 0 ≤ proposal e c)
    (e : G.E) (c : Color)
    (packedU packedV : G.MixedGraphPackedState proposal edgeLabel qLaw R)
    (i j : Fin (explicitLargeSlotBound β qstep r))
    (hpos : 0 < G.mixedGraphLargeProductMass proposal edgeLabel qLaw R
      rho omega e c
      (G.decodeMixedGraphAtom proposal edgeLabel qLaw R
        (G.fst e) packedU c)
      (G.decodeMixedGraphAtom proposal edgeLabel qLaw R
        (G.snd e) packedV c) i j) :
    G.decodeMixedGraphLabel proposal edgeLabel qLaw R
      (G.fst e) packedU c =
        some (edgeLabel (G.fst e) (G.fstStarEdge e)) ∧
    G.decodeMixedGraphLabel proposal edgeLabel qLaw R
      (G.snd e) packedV c =
        some (edgeLabel (G.snd e) (G.sndStarEdge e)) := by
  simpa [decodeMixedGraphLabel] using
    (G.positive_mixedGraphLargeProductMass_endpointLabels
      proposal edgeLabel qLaw R hq0 hqsum hqsingle
      hs hqstep hr0 hleft homega0 homega1 hrho hproposal0 e c
      (G.decodeMixedGraphAtom proposal edgeLabel qLaw R
        (G.fst e) packedU c)
      (G.decodeMixedGraphAtom proposal edgeLabel qLaw R
        (G.snd e) packedV c) i j hpos)

/-- The same endpoint-label certificate holds for a positive tiny-edge
product option after decoding the selected packed words. -/
theorem positive_decoded_mixedGraphTinyProductMass_endpointLabels
    (hq0 : ∀ v c S, 0 ≤ qLaw v c S)
    (hqsum : ∀ v c, ∑ S, qLaw v c S = 1)
    (hqsingle : ∀ v c S, qLaw v c S ≠ 0 → S ≠ ∅ →
      ∃ label : Label, ∀ f ∈ S, edgeLabel v f = label)
    (hs : 0 ≤ s) (hqstep : 0 ≤ qstep) (hr0 : 0 ≤ r)
    (hleft : 0 ≤ 1 - s * (1 + qstep + r))
    (homega0 : 0 < omega) (homega1 : omega ≤ 1)
    (hrho : 0 ≤ rho) (hproposal0 : ∀ e c, 0 ≤ proposal e c)
    (e : G.E) (c : Color)
    (packedU packedV : G.MixedGraphPackedState proposal edgeLabel qLaw R)
    (hpos : 0 < G.mixedGraphTinyProductMass proposal edgeLabel qLaw R
      rho omega e c
      (G.decodeMixedGraphAtom proposal edgeLabel qLaw R
        (G.fst e) packedU c)
      (G.decodeMixedGraphAtom proposal edgeLabel qLaw R
        (G.snd e) packedV c)) :
    G.decodeMixedGraphLabel proposal edgeLabel qLaw R
      (G.fst e) packedU c =
        some (edgeLabel (G.fst e) (G.fstStarEdge e)) ∧
    G.decodeMixedGraphLabel proposal edgeLabel qLaw R
      (G.snd e) packedV c =
        some (edgeLabel (G.snd e) (G.sndStarEdge e)) := by
  simpa [decodeMixedGraphLabel] using
    (G.positive_mixedGraphTinyProductMass_endpointLabels
      proposal edgeLabel qLaw R hq0 hqsum hqsingle
      hs hqstep hr0 hleft homega0 homega1 hrho hproposal0 e c
      (G.decodeMixedGraphAtom proposal edgeLabel qLaw R
        (G.fst e) packedU c)
      (G.decodeMixedGraphAtom proposal edgeLabel qLaw R
        (G.snd e) packedV c) hpos)

end WeightedMultigraph

end

end WeightedEdgeColoring
