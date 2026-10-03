import WeightedEdgeColoring.SubtwoMixedGraphTinyRowMean

/-!
# Concrete packed-word selection for mixed labelled candidates

Both large slots and tiny reservoirs have constant raw row means, while
their selector coefficients have a fixed star-degree column bound.  This
module joins those checked graph-specific estimates with the generic
finite packed-word selector.
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

theorem mixedCandidateAtomMean_le_one_sub_omega
    (rho omega : ℝ)
    (hq0 : ∀ v c S, 0 ≤ qLaw v c S)
    (hqmarg : ∀ v c (f : G.StarEdge v),
      (∑ S, if f ∈ S then qLaw v c S else 0) = proposal f.1 c)
    (hqsingle : ∀ v c S, qLaw v c S ≠ 0 → S ≠ ∅ →
      ∃ label : Label, ∀ f ∈ S, edgeLabel v f = label)
    (hqsum : ∀ v c, ∑ S, qLaw v c S = 1)
    (hs : 0 ≤ s) (hqstep : 0 ≤ qstep) (hr0 : 0 ≤ r)
    (hleft : 0 ≤ 1 - s * (1 + qstep + r))
    (homega0 : 0 < omega) (homega1 : omega < 1)
    (hrho : 0 ≤ rho) (c : Color)
    (row : G.MixedCandidateRowAt proposal edgeLabel qLaw R c) :
    (∑ source : G.V,
      ∑ z : G.MixedGraphAtom proposal edgeLabel qLaw R source c,
        G.smoothedMixedGraphProbability proposal edgeLabel qLaw R
          omega source c z *
          G.mixedCandidateAtomUse proposal edgeLabel qLaw R
            rho omega source c z row) ≤ rho / (1 - omega) := by
  rcases row with large | tiny
  · exact G.mixedLargeCandidateAtomMean_le_one_sub_omega
      proposal edgeLabel qLaw R rho omega hq0 hqmarg hqsingle hqsum
      hs hqstep hr0 hleft homega0 homega1 hrho c large
  · exact G.mixedTinyCandidateAtomMean_le_one_sub_omega
      proposal edgeLabel qLaw R rho omega hq0 hqmarg hqsingle hqsum
      hs hqstep hr0 hleft homega0 homega1 hrho c tiny

theorem scaledMixedCandidateAtomMean_le_one_sub_omega
    (n : ℕ) (scale rho omega : ℝ)
    (hq0 : ∀ v c S, 0 ≤ qLaw v c S)
    (hqmarg : ∀ v c (f : G.StarEdge v),
      (∑ S, if f ∈ S then qLaw v c S else 0) = proposal f.1 c)
    (hqsingle : ∀ v c S, qLaw v c S ≠ 0 → S ≠ ∅ →
      ∃ label : Label, ∀ f ∈ S, edgeLabel v f = label)
    (hqsum : ∀ v c, ∑ S, qLaw v c S = 1)
    (hs : 0 ≤ s) (hqstep : 0 ≤ qstep) (hr0 : 0 ≤ r)
    (hleft : 0 ≤ 1 - s * (1 + qstep + r))
    (homega0 : 0 < omega) (homega1 : omega < 1)
    (hrho : 0 ≤ rho) (hscale : 0 < scale) (c : Color)
    (row : G.MixedCandidateRowAt proposal edgeLabel qLaw R c) :
    (∑ source : G.V,
      ∑ z : G.MixedGraphAtom proposal edgeLabel qLaw R source c,
        G.smoothedMixedGraphProbability proposal edgeLabel qLaw R
          omega source c z *
          G.scaledMixedCandidateAtomUse proposal edgeLabel qLaw R
            n scale rho omega source c z row) ≤
      (n : ℝ) * (rho / (1 - omega)) / scale := by
  have hraw := G.mixedCandidateAtomMean_le_one_sub_omega
    proposal edgeLabel qLaw R rho omega hq0 hqmarg hqsingle hqsum
    hs hqstep hr0 hleft homega0 homega1 hrho c row
  unfold scaledMixedCandidateAtomUse
  have hrearrange :
      (∑ source : G.V,
        ∑ z : G.MixedGraphAtom proposal edgeLabel qLaw R source c,
          G.smoothedMixedGraphProbability proposal edgeLabel qLaw R
            omega source c z *
            ((n : ℝ) * G.mixedCandidateAtomUse
              proposal edgeLabel qLaw R rho omega source c z row / scale)) =
        (n : ℝ) / scale *
          (∑ source : G.V,
            ∑ z : G.MixedGraphAtom proposal edgeLabel qLaw R source c,
              G.smoothedMixedGraphProbability proposal edgeLabel qLaw R
                omega source c z *
                G.mixedCandidateAtomUse proposal edgeLabel qLaw R
                  rho omega source c z row) := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro source _
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro z _
    ring
  rw [hrearrange]
  have hfactor : 0 ≤ (n : ℝ) / scale :=
    div_nonneg (Nat.cast_nonneg n) hscale.le
  calc
    (n : ℝ) / scale *
        (∑ source : G.V,
          ∑ z : G.MixedGraphAtom proposal edgeLabel qLaw R source c,
            G.smoothedMixedGraphProbability proposal edgeLabel qLaw R
              omega source c z *
              G.mixedCandidateAtomUse proposal edgeLabel qLaw R
                rho omega source c z row) ≤
        (n : ℝ) / scale * (rho / (1 - omega)) :=
      mul_le_mul_of_nonneg_left hraw hfactor
    _ = (n : ℝ) * (rho / (1 - omega)) / scale := by ring

/-- Select one positive-probability mixed packed word per vertex while
controlling every actual large-slot and tiny-reservoir candidate row. -/
theorem exists_mixedGraphPackedWord_candidateRows_lt
    {L n D : ℕ} (hL : 0 < L) (hmult : G.PairMultiplicityAtMost L)
    (hn : 0 < n)
    (hq0 : ∀ v c S, 0 ≤ qLaw v c S)
    (hqmarg : ∀ v c (f : G.StarEdge v),
      (∑ S, if f ∈ S then qLaw v c S else 0) = proposal f.1 c)
    (hqsingle : ∀ v c S, qLaw v c S ≠ 0 → S ≠ ∅ →
      ∃ label : Label, ∀ f ∈ S, edgeLabel v f = label)
    (hqsum : ∀ v c, ∑ S, qLaw v c S = 1)
    (hs : 0 < s) (hqstep : 0 ≤ qstep) (hr0 : 0 ≤ r)
    (hleft : 0 ≤ 1 - s * (1 + qstep + r))
    (homega0 : 0 < omega) (homega1 : omega < 1)
    (hrho : 0 < rho) (hC0 : 0 < C0)
    (hproposal0 : ∀ e c, 0 ≤ proposal e c)
    (hproposal : ∀ e c, proposal e c ≤ C0 / (n : ℝ))
    (hdegree : ∀ v, Fintype.card (G.StarEdge v) ≤ D * n) :
    let scale := (L : ℝ) * mixedCandidateOrientedScale (Label := Label)
      (β := β) (qstep := qstep) (r := r) rho s omega C0
    let meanBound := (n : ℝ) * (rho / (1 - omega)) / scale
    let columnBound := mixedCandidatePerColorColumnBound (Label := Label)
      (β := β) (qstep := qstep) (r := r) D n
    ∃ choice : ∀ v : G.V,
      G.MixedGraphPackedState proposal edgeLabel qLaw R,
      (∀ v, 0 < G.paddedMixedGraphWordProbability
        proposal edgeLabel qLaw R omega v (choice v)) ∧
      ∀ row : Σ c : Color,
        G.MixedCandidateRowAt proposal edgeLabel qLaw R c,
        (∑ v : G.V,
          G.scaledMixedCandidateAtomUse proposal edgeLabel qLaw R n
            scale rho omega v row.1
            (G.decodeMixedGraphAtom proposal edgeLabel qLaw R
              v (choice v) row.1) row.2) <
          meanBound + FinitePartialResamplingNumerics.packingDeviation
            meanBound (Fintype.card Color * columnBound) := by
  classical
  let baseScale := mixedCandidateOrientedScale (Label := Label)
    (β := β) (qstep := qstep) (r := r) rho s omega C0
  let scale := (L : ℝ) * baseScale
  let meanBound := (n : ℝ) * (rho / (1 - omega)) / scale
  let columnBound := mixedCandidatePerColorColumnBound (Label := Label)
    (β := β) (qstep := qstep) (r := r) D n
  have hbase : 0 < baseScale := mixedCandidateOrientedScale_pos
    hrho hs homega0 hC0
  have hscale : 0 < scale := by
    have hLreal : (0 : ℝ) < L := by exact_mod_cast hL
    exact mul_pos hLreal hbase
  have hmeanBound : 0 < meanBound := by
    unfold meanBound
    have hnR : (0 : ℝ) < n := by exact_mod_cast hn
    exact div_pos (mul_pos hnR
      (div_pos hrho (sub_pos.mpr homega1))) hscale
  have hcolumnBound : 0 ≤ columnBound := by
    unfold columnBound mixedCandidatePerColorColumnBound
    positivity
  have hatom0 : ∀ v c z row,
      0 ≤ G.scaledMixedCandidateAtomUse proposal edgeLabel qLaw R n
        scale rho omega v c z row := by
    intro v c z row
    unfold scaledMixedCandidateAtomUse
    exact div_nonneg
      (mul_nonneg (Nat.cast_nonneg n)
        (G.mixedCandidateAtomUse_nonneg
          proposal edgeLabel qLaw R hq0 hqsum hqsingle
          hs.le hqstep hr0 hleft homega0 homega1.le
          hrho.le hproposal0 v c z row)) hscale.le
  have hatom1 : ∀ v c z row,
      G.scaledMixedCandidateAtomUse proposal edgeLabel qLaw R n
        scale rho omega v c z row ≤ 1 := by
    intro v c z row
    exact G.scaledMixedCandidateAtomUse_le_one
      proposal edgeLabel qLaw R hL hmult hn hq0 hqmarg hqsingle hqsum
      hs hqstep hr0 hleft homega0 homega1.le hrho hC0
      hproposal0 hproposal v c z row
  have hmean : ∀ c row,
      (∑ v : G.V,
        ∑ z : G.MixedGraphAtom proposal edgeLabel qLaw R v c,
          G.smoothedMixedGraphProbability proposal edgeLabel qLaw R
            omega v c z *
            G.scaledMixedCandidateAtomUse proposal edgeLabel qLaw R n
              scale rho omega v c z row) ≤ meanBound := by
    intro c row
    exact G.scaledMixedCandidateAtomMean_le_one_sub_omega
      proposal edgeLabel qLaw R n scale rho omega
      hq0 hqmarg hqsingle hqsum hs.le hqstep hr0 hleft
      homega0 homega1 hrho.le hscale c row
  have hcolumn : ∀ v c z,
      (∑ row : G.MixedCandidateRowAt proposal edgeLabel qLaw R c,
        G.scaledMixedCandidateAtomUse proposal edgeLabel qLaw R n
          scale rho omega v c z row) ≤ columnBound := by
    intro v c z
    exact G.sum_scaledMixedCandidateAtomUse_mul_le_column
      proposal edgeLabel qLaw R hL hn hq0 hqmarg hqsingle hqsum
      hs hqstep hr0 hleft homega0 homega1.le hrho hC0
      hproposal0 hproposal hdegree v c z
  exact G.exists_mixedGraphPackedWord_capacity_lt
    (RowAt := fun c ↦ G.MixedCandidateRowAt proposal edgeLabel qLaw R c)
    proposal edgeLabel qLaw R omega meanBound columnBound
    hq0 hqsum hqsingle hs.le hqstep hr0 hleft
    homega0 homega1.le hmeanBound hcolumnBound
    (fun v c z row ↦ G.scaledMixedCandidateAtomUse
      proposal edgeLabel qLaw R n scale rho omega v c z row)
    hatom0 hatom1 hmean hcolumn

end WeightedMultigraph

end

end WeightedEdgeColoring
