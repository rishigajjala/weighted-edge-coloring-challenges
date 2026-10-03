import WeightedEdgeColoring.SubtwoMixedGraphWeightedCandidateColumns

/-! Per-edge weighted coefficients for large and tiny candidate rows. -/

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

theorem mixedLargeCandidateEdgeUse_eq_zero_of_tiny
    (rho omega : ℝ) (source : G.V) (c : Color)
    (sourceAtom : G.MixedGraphAtom proposal edgeLabel qLaw R source c)
    (e : G.E) (row : G.MixedLargeCandidateRow
      proposal edgeLabel qLaw R c)
    (htiny : G.weight e < β) :
    G.mixedLargeCandidateEdgeUse proposal edgeLabel qLaw R
      rho omega source c sourceAtom e row = 0 := by
  have hmass : G.mixedGraphLargeEdgeMass proposal s β e c = 0 := by
    simp [mixedGraphLargeEdgeMass, not_le.mpr htiny]
  have hproduct : ∀
      (a : G.MixedGraphAtom proposal edgeLabel qLaw R (G.fst e) c)
      (b : G.MixedGraphAtom proposal edgeLabel qLaw R (G.snd e) c)
      (i j : Fin (explicitLargeSlotBound β qstep r)),
      G.mixedGraphLargeProductMass proposal edgeLabel qLaw R
        rho omega e c a b i j = 0 := by
    intro a b i j
    simp [mixedGraphLargeProductMass, pairedOption, hmass]
  unfold mixedLargeCandidateEdgeUse
  split
  · simp [hproduct]
  · split
    · simp [hproduct]
    · rfl

theorem n_mul_mixedTinyCandidateEdgeUse_le_weight_scale
    {n : ℕ} (hn : 0 < n)
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
    (source : G.V) (c : Color)
    (sourceAtom : G.MixedGraphAtom proposal edgeLabel qLaw R source c)
    (e : G.E) (row : G.MixedTinyCandidateRow
      proposal edgeLabel qLaw R c) :
    (n : ℝ) * G.mixedTinyCandidateEdgeUse
      proposal edgeLabel qLaw R rho omega source c sourceAtom e row ≤
      G.weight e * mixedCandidateOrientedScale (Label := Label)
        (β := β) (qstep := qstep) (r := r) rho s omega C0 := by
  let baseScale := mixedGraphCandidateCapacityScale (Label := Label)
    (β := β) (qstep := qstep) (r := r) rho s omega C0
  have hbase : baseScale ≤ mixedCandidateOrientedScale (Label := Label)
      (β := β) (qstep := qstep) (r := r) rho s omega C0 := by
    unfold mixedCandidateOrientedScale
    have hbase0 : 0 ≤ baseScale := by
      dsimp [baseScale, mixedGraphCandidateCapacityScale]
      positivity
    have hslot : 0 ≤ (explicitLargeSlotBound β qstep r : ℝ) := by positivity
    nlinarith
  have hbound : ∀
      (a : G.MixedGraphAtom proposal edgeLabel qLaw R (G.fst e) c)
      (b : G.MixedGraphAtom proposal edgeLabel qLaw R (G.snd e) c),
      (n : ℝ) * (G.weight e *
        G.mixedGraphTinyProductMass proposal edgeLabel qLaw R
          rho omega e c a b) ≤
      G.weight e * mixedCandidateOrientedScale (Label := Label)
        (β := β) (qstep := qstep) (r := r) rho s omega C0 := by
    intro a b
    exact (G.n_mul_weight_mul_mixedGraphTinyProductMass_le
      proposal edgeLabel qLaw R hn hq0 hqmarg hqsingle hqsum
      hs hqstep hr0 hleft homega0 homega1 hrho hC0
      hproposal0 hproposal e c a b).trans
      (mul_le_mul_of_nonneg_left hbase (G.weight_pos e).le)
  unfold mixedTinyCandidateEdgeUse
  split
  · rename_i hmatch
    exact hbound (hmatch.1 ▸ row.candidate) (hmatch.2 ▸ sourceAtom)
  · split
    · rename_i hmatch
      exact hbound (hmatch.2 ▸ sourceAtom) (hmatch.1 ▸ row.candidate)
    · simpa using mul_nonneg (G.weight_pos e).le
        (mixedCandidateOrientedScale_nonneg (Label := Label)
          (β := β) (qstep := qstep) (r := r)
          hrho hs homega0 hC0)

end WeightedMultigraph

end

end WeightedEdgeColoring
