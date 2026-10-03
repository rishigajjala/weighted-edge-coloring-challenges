import WeightedEdgeColoring.SubtwoMixedGraphCandidateOptions

/-!
# Coefficient bounds for actual mixed labelled candidates

Each oriented candidate edge term is nonnegative.  Both large-edge
orientations have the same fixed diffuse envelope; the second orientation
uses the finite slot count in the common alphabet.  The tiny-edge term
keeps its edge weight, as needed for reservoir capacity rows.
-/

namespace WeightedEdgeColoring

open scoped BigOperators

noncomputable section

theorem pairedOption_nonneg_of
    {PU PV IU IV : Type*}
    (rho y : ℝ) (lambdaU : PU → ℝ) (lambdaV : PV → ℝ)
    (aU : PU → IU → ℝ) (aV : PV → IV → ℝ)
    (p : PU) (q : PV) (i : IU) (j : IV)
    (hrho : 0 ≤ rho) (hy0 : 0 ≤ y)
    (hlamU : 0 ≤ lambdaU p) (hlamV : 0 ≤ lambdaV q)
    (ha0 : 0 ≤ aU p i) (hb0 : 0 ≤ aV q j) :
    0 ≤ pairedOption rho y lambdaU lambdaV aU aV p q i j := by
  unfold pairedOption
  split
  · exact le_rfl
  · exact div_nonneg
      (mul_nonneg (mul_nonneg hrho ha0) hb0)
      (mul_nonneg (mul_nonneg hy0 hlamU) hlamV)

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

def mixedCandidateOrientedScale (rho s omega C0 : ℝ) : ℝ :=
  ((explicitLargeSlotBound β qstep r : ℝ) + 1) *
    mixedGraphCandidateCapacityScale (Label := Label)
      (β := β) (qstep := qstep) (r := r) rho s omega C0

theorem mixedCandidateOrientedScale_nonneg
    (hrho : 0 ≤ rho) (hs : 0 ≤ s)
    (homega0 : 0 < omega) (hC0 : 0 ≤ C0) :
    0 ≤ mixedCandidateOrientedScale (Label := Label)
      (β := β) (qstep := qstep) (r := r) rho s omega C0 := by
  unfold mixedCandidateOrientedScale mixedGraphCandidateCapacityScale
  positivity

theorem mixedGraphLargeProductMass_nonneg
    (hq0 : ∀ v c S, 0 ≤ qLaw v c S)
    (hqsum : ∀ v c, ∑ S, qLaw v c S = 1)
    (hqsingle : ∀ v c S, qLaw v c S ≠ 0 → S ≠ ∅ →
      ∃ label : Label, ∀ f ∈ S, edgeLabel v f = label)
    (hs : 0 ≤ s) (hqstep : 0 ≤ qstep) (hr0 : 0 ≤ r)
    (hleft : 0 ≤ 1 - s * (1 + qstep + r))
    (homega0 : 0 < omega) (homega1 : omega ≤ 1)
    (hrho : 0 ≤ rho) (hproposal0 : ∀ e c, 0 ≤ proposal e c)
    (e : G.E) (c : Color)
    (a : G.MixedGraphAtom proposal edgeLabel qLaw R (G.fst e) c)
    (b : G.MixedGraphAtom proposal edgeLabel qLaw R (G.snd e) c)
    (i j : Fin (explicitLargeSlotBound β qstep r)) :
    0 ≤ G.mixedGraphLargeProductMass proposal edgeLabel qLaw R
      rho omega e c a b i j := by
  unfold mixedGraphLargeProductMass
  apply pairedOption_nonneg_of
  · exact hrho
  · unfold mixedGraphLargeEdgeMass
    split
    · exact mul_nonneg hs (hproposal0 e c)
    · exact le_rfl
  · exact (G.smoothedMixedGraphProbability_pos
      proposal edgeLabel qLaw R hq0 hqsum hqsingle
      hs hqstep hr0 hleft homega0 homega1 (G.fst e) c a).le
  · exact (G.smoothedMixedGraphProbability_pos
      proposal edgeLabel qLaw R hq0 hqsum hqsingle
      hs hqstep hr0 hleft homega0 homega1 (G.snd e) c b).le
  · exact G.mixedGraphLargeAssign_nonneg
      proposal edgeLabel qLaw R hq0 (G.fst e) c (G.fstStarEdge e) a i
  · exact G.mixedGraphLargeAssign_nonneg
      proposal edgeLabel qLaw R hq0 (G.snd e) c (G.sndStarEdge e) b j

theorem mixedGraphTinyProductMass_nonneg
    (hq0 : ∀ v c S, 0 ≤ qLaw v c S)
    (hqsum : ∀ v c, ∑ S, qLaw v c S = 1)
    (hqsingle : ∀ v c S, qLaw v c S ≠ 0 → S ≠ ∅ →
      ∃ label : Label, ∀ f ∈ S, edgeLabel v f = label)
    (hs : 0 ≤ s) (hqstep : 0 ≤ qstep) (hr0 : 0 ≤ r)
    (hleft : 0 ≤ 1 - s * (1 + qstep + r))
    (homega0 : 0 < omega) (homega1 : omega ≤ 1)
    (hrho : 0 ≤ rho) (hproposal0 : ∀ e c, 0 ≤ proposal e c)
    (e : G.E) (c : Color)
    (a : G.MixedGraphAtom proposal edgeLabel qLaw R (G.fst e) c)
    (b : G.MixedGraphAtom proposal edgeLabel qLaw R (G.snd e) c) :
    0 ≤ G.mixedGraphTinyProductMass proposal edgeLabel qLaw R
      rho omega e c a b := by
  unfold mixedGraphTinyProductMass
  apply pairedOption_nonneg_of
  · exact hrho
  · unfold mixedGraphTinyEdgeMass
    split
    · exact mul_nonneg hs (hproposal0 e c)
    · exact le_rfl
  · exact (G.smoothedMixedGraphProbability_pos
      proposal edgeLabel qLaw R hq0 hqsum hqsingle
      hs hqstep hr0 hleft homega0 homega1 (G.fst e) c a).le
  · exact (G.smoothedMixedGraphProbability_pos
      proposal edgeLabel qLaw R hq0 hqsum hqsingle
      hs hqstep hr0 hleft homega0 homega1 (G.snd e) c b).le
  · exact G.mixedGraphTinyAssign_nonneg
      proposal edgeLabel qLaw R hq0 (G.fst e) c (G.fstStarEdge e) a
  · exact G.mixedGraphTinyAssign_nonneg
      proposal edgeLabel qLaw R hq0 (G.snd e) c (G.sndStarEdge e) b

theorem n_mul_mixedLargeCandidateEdgeUse_le_scale
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
    (e : G.E) (row : G.MixedLargeCandidateRow
      proposal edgeLabel qLaw R c) :
    (n : ℝ) * G.mixedLargeCandidateEdgeUse
      proposal edgeLabel qLaw R rho omega source c sourceAtom e row ≤
      mixedCandidateOrientedScale (Label := Label)
        (β := β) (qstep := qstep) (r := r) rho s omega C0 := by
  let baseScale := mixedGraphCandidateCapacityScale (Label := Label)
    (β := β) (qstep := qstep) (r := r) rho s omega C0
  have hbase0 : 0 ≤ baseScale := by
    unfold baseScale mixedGraphCandidateCapacityScale
    positivity
  have hscale0 : 0 ≤ mixedCandidateOrientedScale (Label := Label)
      (β := β) (qstep := qstep) (r := r) rho s omega C0 :=
    mixedCandidateOrientedScale_nonneg hrho hs homega0 hC0
  unfold mixedLargeCandidateEdgeUse
  split
  · rename_i hmatch
    have hbound := G.n_mul_sum_mixedGraphLargeProductMass_le_scale
      proposal edgeLabel qLaw R hn hq0 hqmarg hqsingle hqsum
      hs hqstep hr0 hleft homega0 homega1 hrho hC0
      hproposal0 hproposal e c (hmatch.1 ▸ row.candidate)
      (hmatch.2 ▸ sourceAtom) row.slot
    exact hbound.trans (by
      unfold mixedCandidateOrientedScale
      nlinarith)
  · split
    · rename_i hmatch
      have hterm : ∀ i : Fin (explicitLargeSlotBound β qstep r),
          (n : ℝ) * G.mixedGraphLargeProductMass
            proposal edgeLabel qLaw R rho omega e c
            (hmatch.2 ▸ sourceAtom) (hmatch.1 ▸ row.candidate)
            i row.slot ≤ baseScale := by
        intro i
        have hsingle :
            G.mixedGraphLargeProductMass
              proposal edgeLabel qLaw R rho omega e c
              (hmatch.2 ▸ sourceAtom) (hmatch.1 ▸ row.candidate)
              i row.slot ≤
            ∑ j, G.mixedGraphLargeProductMass
              proposal edgeLabel qLaw R rho omega e c
              (hmatch.2 ▸ sourceAtom) (hmatch.1 ▸ row.candidate)
              i j :=
          Finset.single_le_sum
            (fun j _ ↦ G.mixedGraphLargeProductMass_nonneg
              proposal edgeLabel qLaw R hq0 hqsum hqsingle
              hs hqstep hr0 hleft homega0 homega1
              hrho hproposal0 e c
              (hmatch.2 ▸ sourceAtom) (hmatch.1 ▸ row.candidate)
              i j)
            (Finset.mem_univ row.slot)
        exact (mul_le_mul_of_nonneg_left hsingle
          (Nat.cast_nonneg n)).trans
          (G.n_mul_sum_mixedGraphLargeProductMass_le_scale
            proposal edgeLabel qLaw R hn hq0 hqmarg hqsingle hqsum
            hs hqstep hr0 hleft homega0 homega1 hrho hC0
            hproposal0 hproposal e c
            (hmatch.2 ▸ sourceAtom) (hmatch.1 ▸ row.candidate) i)
      calc
        (n : ℝ) * (∑ i,
          G.mixedGraphLargeProductMass proposal edgeLabel qLaw R
            rho omega e c (hmatch.2 ▸ sourceAtom)
              (hmatch.1 ▸ row.candidate) i row.slot) =
          ∑ i, (n : ℝ) * G.mixedGraphLargeProductMass
            proposal edgeLabel qLaw R rho omega e c
            (hmatch.2 ▸ sourceAtom) (hmatch.1 ▸ row.candidate)
            i row.slot := by rw [Finset.mul_sum]
        _ ≤ ∑ _i : Fin (explicitLargeSlotBound β qstep r),
            baseScale := Finset.sum_le_sum fun i _ ↦ hterm i
        _ ≤ mixedCandidateOrientedScale (Label := Label)
            (β := β) (qstep := qstep) (r := r) rho s omega C0 := by
          simp [mixedCandidateOrientedScale, baseScale]
          nlinarith
    · simpa using hscale0

theorem n_mul_mixedTinyCandidateEdgeUse_le_scale
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
      mixedCandidateOrientedScale (Label := Label)
        (β := β) (qstep := qstep) (r := r) rho s omega C0 := by
  let baseScale := mixedGraphCandidateCapacityScale (Label := Label)
    (β := β) (qstep := qstep) (r := r) rho s omega C0
  have hbase0 : 0 ≤ baseScale := by
    unfold baseScale mixedGraphCandidateCapacityScale
    positivity
  have hscale0 : 0 ≤ mixedCandidateOrientedScale (Label := Label)
      (β := β) (qstep := qstep) (r := r) rho s omega C0 :=
    mixedCandidateOrientedScale_nonneg hrho hs homega0 hC0
  have hbound : ∀
      (a : G.MixedGraphAtom proposal edgeLabel qLaw R (G.fst e) c)
      (b : G.MixedGraphAtom proposal edgeLabel qLaw R (G.snd e) c),
      (n : ℝ) * (G.weight e *
        G.mixedGraphTinyProductMass proposal edgeLabel qLaw R
          rho omega e c a b) ≤
        mixedCandidateOrientedScale (Label := Label)
          (β := β) (qstep := qstep) (r := r) rho s omega C0 := by
    intro a b
    calc
      (n : ℝ) * (G.weight e *
        G.mixedGraphTinyProductMass proposal edgeLabel qLaw R
          rho omega e c a b) ≤ G.weight e * baseScale :=
        G.n_mul_weight_mul_mixedGraphTinyProductMass_le
          proposal edgeLabel qLaw R hn hq0 hqmarg hqsingle hqsum
          hs hqstep hr0 hleft homega0 homega1 hrho hC0
          hproposal0 hproposal e c a b
      _ ≤ baseScale := mul_le_of_le_one_left hbase0 (G.weight_le_one e)
      _ ≤ mixedCandidateOrientedScale (Label := Label)
          (β := β) (qstep := qstep) (r := r) rho s omega C0 := by
        unfold mixedCandidateOrientedScale
        nlinarith
  unfold mixedTinyCandidateEdgeUse
  split
  · rename_i hmatch
    exact hbound (hmatch.1 ▸ row.candidate) (hmatch.2 ▸ sourceAtom)
  · split
    · rename_i hmatch
      exact hbound (hmatch.2 ▸ sourceAtom) (hmatch.1 ▸ row.candidate)
    · simpa using hscale0

theorem mixedLargeCandidateEdgeUse_nonneg
    (hq0 : ∀ v c S, 0 ≤ qLaw v c S)
    (hqsum : ∀ v c, ∑ S, qLaw v c S = 1)
    (hqsingle : ∀ v c S, qLaw v c S ≠ 0 → S ≠ ∅ →
      ∃ label : Label, ∀ f ∈ S, edgeLabel v f = label)
    (hs : 0 ≤ s) (hqstep : 0 ≤ qstep) (hr0 : 0 ≤ r)
    (hleft : 0 ≤ 1 - s * (1 + qstep + r))
    (homega0 : 0 < omega) (homega1 : omega ≤ 1)
    (hrho : 0 ≤ rho) (hproposal0 : ∀ e c, 0 ≤ proposal e c)
    (source : G.V) (c : Color)
    (sourceAtom : G.MixedGraphAtom proposal edgeLabel qLaw R source c)
    (e : G.E) (row : G.MixedLargeCandidateRow
      proposal edgeLabel qLaw R c) :
    0 ≤ G.mixedLargeCandidateEdgeUse proposal edgeLabel qLaw R
      rho omega source c sourceAtom e row := by
  unfold mixedLargeCandidateEdgeUse
  split
  · rename_i hmatch
    exact Finset.sum_nonneg fun j _ ↦
      G.mixedGraphLargeProductMass_nonneg
        proposal edgeLabel qLaw R hq0 hqsum hqsingle
        hs hqstep hr0 hleft homega0 homega1 hrho hproposal0
        e c (hmatch.1 ▸ row.candidate) (hmatch.2 ▸ sourceAtom)
        row.slot j
  · split
    · rename_i hmatch
      exact Finset.sum_nonneg fun i _ ↦
        G.mixedGraphLargeProductMass_nonneg
          proposal edgeLabel qLaw R hq0 hqsum hqsingle
          hs hqstep hr0 hleft homega0 homega1 hrho hproposal0
          e c (hmatch.2 ▸ sourceAtom) (hmatch.1 ▸ row.candidate)
          i row.slot
    · exact le_rfl

theorem mixedTinyCandidateEdgeUse_nonneg
    (hq0 : ∀ v c S, 0 ≤ qLaw v c S)
    (hqsum : ∀ v c, ∑ S, qLaw v c S = 1)
    (hqsingle : ∀ v c S, qLaw v c S ≠ 0 → S ≠ ∅ →
      ∃ label : Label, ∀ f ∈ S, edgeLabel v f = label)
    (hs : 0 ≤ s) (hqstep : 0 ≤ qstep) (hr0 : 0 ≤ r)
    (hleft : 0 ≤ 1 - s * (1 + qstep + r))
    (homega0 : 0 < omega) (homega1 : omega ≤ 1)
    (hrho : 0 ≤ rho) (hproposal0 : ∀ e c, 0 ≤ proposal e c)
    (source : G.V) (c : Color)
    (sourceAtom : G.MixedGraphAtom proposal edgeLabel qLaw R source c)
    (e : G.E) (row : G.MixedTinyCandidateRow
      proposal edgeLabel qLaw R c) :
    0 ≤ G.mixedTinyCandidateEdgeUse proposal edgeLabel qLaw R
      rho omega source c sourceAtom e row := by
  unfold mixedTinyCandidateEdgeUse
  split
  · rename_i hmatch
    exact mul_nonneg (G.weight_nonneg e)
      (G.mixedGraphTinyProductMass_nonneg
        proposal edgeLabel qLaw R hq0 hqsum hqsingle
        hs hqstep hr0 hleft homega0 homega1 hrho hproposal0
        e c (hmatch.1 ▸ row.candidate) (hmatch.2 ▸ sourceAtom))
  · split
    · rename_i hmatch
      exact mul_nonneg (G.weight_nonneg e)
        (G.mixedGraphTinyProductMass_nonneg
          proposal edgeLabel qLaw R hq0 hqsum hqsingle
          hs hqstep hr0 hleft homega0 homega1 hrho hproposal0
          e c (hmatch.2 ▸ sourceAtom) (hmatch.1 ▸ row.candidate))
    · exact le_rfl

theorem mixedCandidateAtomUse_nonneg
    (hq0 : ∀ v c S, 0 ≤ qLaw v c S)
    (hqsum : ∀ v c, ∑ S, qLaw v c S = 1)
    (hqsingle : ∀ v c S, qLaw v c S ≠ 0 → S ≠ ∅ →
      ∃ label : Label, ∀ f ∈ S, edgeLabel v f = label)
    (hs : 0 ≤ s) (hqstep : 0 ≤ qstep) (hr0 : 0 ≤ r)
    (hleft : 0 ≤ 1 - s * (1 + qstep + r))
    (homega0 : 0 < omega) (homega1 : omega ≤ 1)
    (hrho : 0 ≤ rho) (hproposal0 : ∀ e c, 0 ≤ proposal e c)
    (source : G.V) (c : Color)
    (sourceAtom : G.MixedGraphAtom proposal edgeLabel qLaw R source c)
    (row : G.MixedCandidateRowAt proposal edgeLabel qLaw R c) :
    0 ≤ G.mixedCandidateAtomUse proposal edgeLabel qLaw R
      rho omega source c sourceAtom row := by
  cases row with
  | inl large =>
      exact Finset.sum_nonneg fun e _ ↦
        G.mixedLargeCandidateEdgeUse_nonneg
          proposal edgeLabel qLaw R hq0 hqsum hqsingle
          hs hqstep hr0 hleft homega0 homega1 hrho hproposal0
          source c sourceAtom e large
  | inr tiny =>
      exact Finset.sum_nonneg fun e _ ↦
        G.mixedTinyCandidateEdgeUse_nonneg
          proposal edgeLabel qLaw R hq0 hqsum hqsingle
          hs hqstep hr0 hleft homega0 homega1 hrho hproposal0
          source c sourceAtom e tiny

end WeightedMultigraph

end

end WeightedEdgeColoring
