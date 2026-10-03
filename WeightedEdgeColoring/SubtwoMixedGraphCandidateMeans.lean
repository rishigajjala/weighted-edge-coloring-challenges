import WeightedEdgeColoring.SubtwoMixedGraphCandidateColumns

/-!
# Endpoint expectations for mixed labelled candidate options

The paired option uses the common unconditional edge mass.  Averaging the
opposite endpoint's mixed atom therefore recovers the fixed endpoint's
actual assignment, divided by its smoothed atom probability.  These are
the edgewise identities needed to bound candidate row means by local slot
and reservoir capacities.
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

theorem mixedGraphLargeProductMass_right_expectation
    (rho omega : ℝ)
    (hq0 : ∀ v c S, 0 ≤ qLaw v c S)
    (hqmarg : ∀ v c (f : G.StarEdge v),
      (∑ S, if f ∈ S then qLaw v c S else 0) = proposal f.1 c)
    (hqsingle : ∀ v c S, qLaw v c S ≠ 0 → S ≠ ∅ →
      ∃ label : Label, ∀ f ∈ S, edgeLabel v f = label)
    (hqsum : ∀ v c, ∑ S, qLaw v c S = 1)
    (hs : 0 ≤ s) (hqstep : 0 ≤ qstep) (hr0 : 0 ≤ r)
    (hleft : 0 ≤ 1 - s * (1 + qstep + r))
    (homega0 : 0 < omega) (homega1 : omega ≤ 1)
    (e : G.E) (c : Color)
    (hy : G.mixedGraphLargeEdgeMass proposal s β e c ≠ 0)
    (a : G.MixedGraphAtom proposal edgeLabel qLaw R (G.fst e) c)
    (i : Fin (explicitLargeSlotBound β qstep r)) :
    (∑ b : G.MixedGraphAtom proposal edgeLabel qLaw R (G.snd e) c,
      G.smoothedMixedGraphProbability proposal edgeLabel qLaw R
        omega (G.snd e) c b * ∑ j,
        G.mixedGraphLargeProductMass proposal edgeLabel qLaw R
          rho omega e c a b i j) =
      rho * G.mixedGraphLargeAssign proposal edgeLabel qLaw R
        (G.fst e) c (G.fstStarEdge e) a i /
        G.smoothedMixedGraphProbability proposal edgeLabel qLaw R
          omega (G.fst e) c a := by
  unfold mixedGraphLargeProductMass
  apply sum_pairedOption_right
  · exact hy
  · exact (G.smoothedMixedGraphProbability_pos
      proposal edgeLabel qLaw R hq0 hqsum hqsingle
      hs hqstep hr0 hleft homega0 homega1 (G.fst e) c a).ne'
  · intro b
    exact (G.smoothedMixedGraphProbability_pos
      proposal edgeLabel qLaw R hq0 hqsum hqsingle
      hs hqstep hr0 hleft homega0 homega1 (G.snd e) c b).ne'
  · simpa [mixedGraphLargeEdgeMass, mixedGraphLargeAssign] using
      G.sum_mixedLabelGraphLargeAssign
        (edgeLabel (G.snd e))
        (fun f : G.StarEdge (G.snd e) ↦ proposal f.1 c)
        (qLaw (G.snd e) c) (R (G.snd e) c)
        (hq0 (G.snd e) c) (hqmarg (G.snd e) c)
        (hqsingle (G.snd e) c) (G.sndStarEdge e)

theorem mixedGraphLargeProductMass_left_expectation
    (rho omega : ℝ)
    (hq0 : ∀ v c S, 0 ≤ qLaw v c S)
    (hqmarg : ∀ v c (f : G.StarEdge v),
      (∑ S, if f ∈ S then qLaw v c S else 0) = proposal f.1 c)
    (hqsingle : ∀ v c S, qLaw v c S ≠ 0 → S ≠ ∅ →
      ∃ label : Label, ∀ f ∈ S, edgeLabel v f = label)
    (hqsum : ∀ v c, ∑ S, qLaw v c S = 1)
    (hs : 0 ≤ s) (hqstep : 0 ≤ qstep) (hr0 : 0 ≤ r)
    (hleft : 0 ≤ 1 - s * (1 + qstep + r))
    (homega0 : 0 < omega) (homega1 : omega ≤ 1)
    (e : G.E) (c : Color)
    (hy : G.mixedGraphLargeEdgeMass proposal s β e c ≠ 0)
    (b : G.MixedGraphAtom proposal edgeLabel qLaw R (G.snd e) c)
    (j : Fin (explicitLargeSlotBound β qstep r)) :
    (∑ a : G.MixedGraphAtom proposal edgeLabel qLaw R (G.fst e) c,
      G.smoothedMixedGraphProbability proposal edgeLabel qLaw R
        omega (G.fst e) c a * ∑ i,
        G.mixedGraphLargeProductMass proposal edgeLabel qLaw R
          rho omega e c a b i j) =
      rho * G.mixedGraphLargeAssign proposal edgeLabel qLaw R
        (G.snd e) c (G.sndStarEdge e) b j /
        G.smoothedMixedGraphProbability proposal edgeLabel qLaw R
          omega (G.snd e) c b := by
  unfold mixedGraphLargeProductMass
  apply sum_pairedOption_left
  · exact hy
  · intro a
    exact (G.smoothedMixedGraphProbability_pos
      proposal edgeLabel qLaw R hq0 hqsum hqsingle
      hs hqstep hr0 hleft homega0 homega1 (G.fst e) c a).ne'
  · exact (G.smoothedMixedGraphProbability_pos
      proposal edgeLabel qLaw R hq0 hqsum hqsingle
      hs hqstep hr0 hleft homega0 homega1 (G.snd e) c b).ne'
  · simpa [mixedGraphLargeEdgeMass, mixedGraphLargeAssign] using
      G.sum_mixedLabelGraphLargeAssign
        (edgeLabel (G.fst e))
        (fun f : G.StarEdge (G.fst e) ↦ proposal f.1 c)
        (qLaw (G.fst e) c) (R (G.fst e) c)
        (hq0 (G.fst e) c) (hqmarg (G.fst e) c)
        (hqsingle (G.fst e) c) (G.fstStarEdge e)

theorem mixedGraphTinyProductMass_right_expectation
    (rho omega : ℝ)
    (hq0 : ∀ v c S, 0 ≤ qLaw v c S)
    (hqmarg : ∀ v c (f : G.StarEdge v),
      (∑ S, if f ∈ S then qLaw v c S else 0) = proposal f.1 c)
    (hqsingle : ∀ v c S, qLaw v c S ≠ 0 → S ≠ ∅ →
      ∃ label : Label, ∀ f ∈ S, edgeLabel v f = label)
    (hqsum : ∀ v c, ∑ S, qLaw v c S = 1)
    (hs : 0 ≤ s) (hqstep : 0 ≤ qstep) (hr0 : 0 ≤ r)
    (hleft : 0 ≤ 1 - s * (1 + qstep + r))
    (homega0 : 0 < omega) (homega1 : omega ≤ 1)
    (e : G.E) (c : Color)
    (hy : G.mixedGraphTinyEdgeMass proposal s β e c ≠ 0)
    (a : G.MixedGraphAtom proposal edgeLabel qLaw R (G.fst e) c) :
    (∑ b : G.MixedGraphAtom proposal edgeLabel qLaw R (G.snd e) c,
      G.smoothedMixedGraphProbability proposal edgeLabel qLaw R
        omega (G.snd e) c b *
        G.mixedGraphTinyProductMass proposal edgeLabel qLaw R
          rho omega e c a b) =
      rho * G.mixedGraphTinyAssign proposal edgeLabel qLaw R
        (G.fst e) c (G.fstStarEdge e) a /
        G.smoothedMixedGraphProbability proposal edgeLabel qLaw R
          omega (G.fst e) c a := by
  have h := sum_pairedOption_right rho
    (G.mixedGraphTinyEdgeMass proposal s β e c)
    (G.smoothedMixedGraphProbability proposal edgeLabel qLaw R
      omega (G.fst e) c)
    (G.smoothedMixedGraphProbability proposal edgeLabel qLaw R
      omega (G.snd e) c)
    (fun a (_ : Fin 1) ↦ G.mixedGraphTinyAssign proposal edgeLabel qLaw R
      (G.fst e) c (G.fstStarEdge e) a)
    (fun b (_ : Fin 1) ↦ G.mixedGraphTinyAssign proposal edgeLabel qLaw R
      (G.snd e) c (G.sndStarEdge e) b)
    a 0 hy
    (G.smoothedMixedGraphProbability_pos
      proposal edgeLabel qLaw R hq0 hqsum hqsingle
      hs hqstep hr0 hleft homega0 homega1 (G.fst e) c a).ne'
    (fun b ↦ (G.smoothedMixedGraphProbability_pos
      proposal edgeLabel qLaw R hq0 hqsum hqsingle
      hs hqstep hr0 hleft homega0 homega1 (G.snd e) c b).ne')
    (by simpa [mixedGraphTinyEdgeMass, mixedGraphTinyAssign] using
      (G.sum_mixedLabelGraphTinyAssign
        (edgeLabel (G.snd e))
        (fun f : G.StarEdge (G.snd e) ↦ proposal f.1 c)
        (qLaw (G.snd e) c) (R (G.snd e) c)
        (hq0 (G.snd e) c) (hqmarg (G.snd e) c)
        (hqsingle (G.snd e) c) (G.sndStarEdge e)))
  simpa [mixedGraphTinyProductMass] using h

theorem mixedGraphTinyProductMass_left_expectation
    (rho omega : ℝ)
    (hq0 : ∀ v c S, 0 ≤ qLaw v c S)
    (hqmarg : ∀ v c (f : G.StarEdge v),
      (∑ S, if f ∈ S then qLaw v c S else 0) = proposal f.1 c)
    (hqsingle : ∀ v c S, qLaw v c S ≠ 0 → S ≠ ∅ →
      ∃ label : Label, ∀ f ∈ S, edgeLabel v f = label)
    (hqsum : ∀ v c, ∑ S, qLaw v c S = 1)
    (hs : 0 ≤ s) (hqstep : 0 ≤ qstep) (hr0 : 0 ≤ r)
    (hleft : 0 ≤ 1 - s * (1 + qstep + r))
    (homega0 : 0 < omega) (homega1 : omega ≤ 1)
    (e : G.E) (c : Color)
    (hy : G.mixedGraphTinyEdgeMass proposal s β e c ≠ 0)
    (b : G.MixedGraphAtom proposal edgeLabel qLaw R (G.snd e) c) :
    (∑ a : G.MixedGraphAtom proposal edgeLabel qLaw R (G.fst e) c,
      G.smoothedMixedGraphProbability proposal edgeLabel qLaw R
        omega (G.fst e) c a *
        G.mixedGraphTinyProductMass proposal edgeLabel qLaw R
          rho omega e c a b) =
      rho * G.mixedGraphTinyAssign proposal edgeLabel qLaw R
        (G.snd e) c (G.sndStarEdge e) b /
        G.smoothedMixedGraphProbability proposal edgeLabel qLaw R
          omega (G.snd e) c b := by
  have h := sum_pairedOption_left rho
    (G.mixedGraphTinyEdgeMass proposal s β e c)
    (G.smoothedMixedGraphProbability proposal edgeLabel qLaw R
      omega (G.fst e) c)
    (G.smoothedMixedGraphProbability proposal edgeLabel qLaw R
      omega (G.snd e) c)
    (fun a (_ : Fin 1) ↦ G.mixedGraphTinyAssign proposal edgeLabel qLaw R
      (G.fst e) c (G.fstStarEdge e) a)
    (fun b (_ : Fin 1) ↦ G.mixedGraphTinyAssign proposal edgeLabel qLaw R
      (G.snd e) c (G.sndStarEdge e) b)
    b 0 hy
    (fun a ↦ (G.smoothedMixedGraphProbability_pos
      proposal edgeLabel qLaw R hq0 hqsum hqsingle
      hs hqstep hr0 hleft homega0 homega1 (G.fst e) c a).ne')
    (G.smoothedMixedGraphProbability_pos
      proposal edgeLabel qLaw R hq0 hqsum hqsingle
      hs hqstep hr0 hleft homega0 homega1 (G.snd e) c b).ne'
    (by simpa [mixedGraphTinyEdgeMass, mixedGraphTinyAssign] using
      (G.sum_mixedLabelGraphTinyAssign
        (edgeLabel (G.fst e))
        (fun f : G.StarEdge (G.fst e) ↦ proposal f.1 c)
        (qLaw (G.fst e) c) (R (G.fst e) c)
        (hq0 (G.fst e) c) (hqmarg (G.fst e) c)
        (hqsingle (G.fst e) c) (G.fstStarEdge e)))
  simpa [mixedGraphTinyProductMass] using h

end WeightedMultigraph

end

end WeightedEdgeColoring
