import WeightedEdgeColoring.SubtwoMixedGraphWeightedColumnBound

/-! Padded mixed words retain the star-weight column bound. -/

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

theorem sum_scaledMixedCandidateAtomUse_mul_le_weightedColumn
    {L n : ℕ} (hL : 0 < L) (hn : 0 < n)
    (hq0 : ∀ v c S, 0 ≤ qLaw v c S)
    (hqmarg : ∀ v c (f : G.StarEdge v),
      (∑ S, if f ∈ S then qLaw v c S else 0) = proposal f.1 c)
    (hqsingle : ∀ v c S, qLaw v c S ≠ 0 → S ≠ ∅ →
      ∃ label : Label, ∀ f ∈ S, edgeLabel v f = label)
    (hqsum : ∀ v c, ∑ S, qLaw v c S = 1)
    (hs : 0 < s) (hqstep : 0 ≤ qstep) (hr0 : 0 ≤ r)
    (hleft : 0 ≤ 1 - s * (1 + qstep + r))
    (homega0 : 0 < omega) (homega1 : omega ≤ 1)
    (hrho : 0 < rho) (hC0 : 0 < C0)
    (hproposal0 : ∀ e c, 0 ≤ proposal e c)
    (hproposal : ∀ e c, proposal e c ≤ C0 / (n : ℝ))
    (hstar : ∀ v, G.starWeight v ≤ n)
    (source : G.V) (c : Color)
    (sourceAtom : G.MixedGraphAtom proposal edgeLabel qLaw R source c) :
    (∑ row : G.MixedCandidateRowAt proposal edgeLabel qLaw R c,
      G.scaledMixedCandidateAtomUse proposal edgeLabel qLaw R n
        ((L : ℝ) * mixedCandidateOrientedScale (Label := Label)
          (β := β) (qstep := qstep) (r := r) rho s omega C0)
        rho omega source c sourceAtom row) ≤
      mixedCandidateWeightedPerColorColumnBound (Label := Label)
        (β := β) (qstep := qstep) (r := r) n := by
  let baseScale := mixedCandidateOrientedScale (Label := Label)
    (β := β) (qstep := qstep) (r := r) rho s omega C0
  have hbase : 0 < baseScale := mixedCandidateOrientedScale_pos
    hrho hs homega0 hC0
  have hLreal : (1 : ℝ) ≤ L := by exact_mod_cast hL
  have hscale : 0 < (L : ℝ) * baseScale := by positivity
  calc
    (∑ row : G.MixedCandidateRowAt proposal edgeLabel qLaw R c,
      G.scaledMixedCandidateAtomUse proposal edgeLabel qLaw R n
        ((L : ℝ) * baseScale) rho omega source c sourceAtom row) ≤
        ∑ row : G.MixedCandidateRowAt proposal edgeLabel qLaw R c,
          G.scaledMixedCandidateAtomUse proposal edgeLabel qLaw R n
            baseScale rho omega source c sourceAtom row := by
      apply Finset.sum_le_sum
      intro row _
      unfold scaledMixedCandidateAtomUse
      apply (div_le_div_iff₀ hscale hbase).2
      have huse := G.mixedCandidateAtomUse_nonneg
        proposal edgeLabel qLaw R hq0 hqsum hqsingle
        hs.le hqstep hr0 hleft homega0 homega1 hrho.le hproposal0
        source c sourceAtom row
      have hnum : 0 ≤ (n : ℝ) *
          G.mixedCandidateAtomUse proposal edgeLabel qLaw R
            rho omega source c sourceAtom row :=
        mul_nonneg (Nat.cast_nonneg n) huse
      exact mul_le_mul_of_nonneg_left
        (by simpa using mul_le_mul_of_nonneg_right hLreal hbase.le) hnum
    _ ≤ mixedCandidateWeightedPerColorColumnBound (Label := Label)
        (β := β) (qstep := qstep) (r := r) n := by
      simpa [baseScale] using
        G.sum_scaledMixedCandidateAtomUse_le_weightedColumn
          proposal edgeLabel qLaw R hn hq0 hqmarg hqsingle hqsum
          hs hqstep hr0 hleft homega0 homega1 hrho hC0
          hproposal0 hproposal hstar source c sourceAtom

theorem sum_scaledMixedPackedWordCandidateUse_mul_le_weightedColumn
    {L n : ℕ} (hL : 0 < L) (hn : 0 < n)
    (hq0 : ∀ v c S, 0 ≤ qLaw v c S)
    (hqmarg : ∀ v c (f : G.StarEdge v),
      (∑ S, if f ∈ S then qLaw v c S else 0) = proposal f.1 c)
    (hqsingle : ∀ v c S, qLaw v c S ≠ 0 → S ≠ ∅ →
      ∃ label : Label, ∀ f ∈ S, edgeLabel v f = label)
    (hqsum : ∀ v c, ∑ S, qLaw v c S = 1)
    (hs : 0 < s) (hqstep : 0 ≤ qstep) (hr0 : 0 ≤ r)
    (hleft : 0 ≤ 1 - s * (1 + qstep + r))
    (homega0 : 0 < omega) (homega1 : omega ≤ 1)
    (hrho : 0 < rho) (hC0 : 0 < C0)
    (hproposal0 : ∀ e c, 0 ≤ proposal e c)
    (hproposal : ∀ e c, proposal e c ≤ C0 / (n : ℝ))
    (hstar : ∀ v, G.starWeight v ≤ n)
    (source : G.V)
    (packed : G.MixedGraphPackedState proposal edgeLabel qLaw R) :
    (∑ c : Color,
      ∑ row : G.MixedCandidateRowAt proposal edgeLabel qLaw R c,
        G.scaledMixedCandidateAtomUse proposal edgeLabel qLaw R n
          ((L : ℝ) * mixedCandidateOrientedScale (Label := Label)
            (β := β) (qstep := qstep) (r := r) rho s omega C0)
          rho omega source c
          (G.decodeMixedGraphAtom proposal edgeLabel qLaw R source packed c)
          row) ≤
      (Fintype.card Color : ℝ) *
        mixedCandidateWeightedPerColorColumnBound (Label := Label)
          (β := β) (qstep := qstep) (r := r) n := by
  calc
    (∑ c : Color,
      ∑ row : G.MixedCandidateRowAt proposal edgeLabel qLaw R c,
        G.scaledMixedCandidateAtomUse proposal edgeLabel qLaw R n
          ((L : ℝ) * mixedCandidateOrientedScale (Label := Label)
            (β := β) (qstep := qstep) (r := r) rho s omega C0)
          rho omega source c
          (G.decodeMixedGraphAtom proposal edgeLabel qLaw R source packed c)
          row) ≤
        ∑ _c : Color,
          mixedCandidateWeightedPerColorColumnBound (Label := Label)
            (β := β) (qstep := qstep) (r := r) n := by
      apply Finset.sum_le_sum
      intro c _
      exact G.sum_scaledMixedCandidateAtomUse_mul_le_weightedColumn
        proposal edgeLabel qLaw R hL hn hq0 hqmarg hqsingle hqsum
        hs hqstep hr0 hleft homega0 homega1 hrho hC0
        hproposal0 hproposal hstar source c
        (G.decodeMixedGraphAtom proposal edgeLabel qLaw R source packed c)
    _ = (Fintype.card Color : ℝ) *
        mixedCandidateWeightedPerColorColumnBound (Label := Label)
          (β := β) (qstep := qstep) (r := r) n := by simp

end WeightedMultigraph

end

end WeightedEdgeColoring
