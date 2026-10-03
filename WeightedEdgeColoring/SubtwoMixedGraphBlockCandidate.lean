import WeightedEdgeColoring.SubtwoMixedGraphBlockVarianceRows
import WeightedEdgeColoring.SubtwoMixedGraphWeightedJointSelection

/-! Candidate capacity coefficients on fixed, independently selected mixed blocks. -/

namespace WeightedEdgeColoring

open scoped BigOperators

noncomputable section

namespace WeightedMultigraph

variable (G : WeightedMultigraph)
variable {B k : ℕ} {Label : Type*} [Fintype Label] [DecidableEq Label]
variable (proposal : G.E → (Fin B × Fin k) → ℝ)
variable (edgeLabel : ∀ v : G.V, G.StarEdge v → Label)
variable (qLaw : ∀ v : G.V, (Fin B × Fin k) →
  Finset (G.StarEdge v) → ℝ)
variable {s β qstep r : ℝ} {hβ : 0 < β} {hr : 0 < r}
variable (R : ∀ v c label,
  G.BoundedProfileRealization
    (G.conditionalEndpointProposal (edgeLabel v)
      (fun e : G.StarEdge v ↦ proposal e.1 c) (qLaw v c) label)
    s β qstep r hβ hr)

abbrev MixedBlockCapacityRow :=
  Σ c : Fin B × Fin k,
    G.MixedCandidateRowAt proposal edgeLabel qLaw R c

def mixedBlockCandidateUse
    (n : ℕ) (scale rho omega : ℝ)
    (source : G.V × Fin B)
    (state : G.MixedGraphPackedBlockState
      proposal edgeLabel qLaw R source.2)
    (row : G.MixedBlockCapacityRow proposal edgeLabel qLaw R) : ℝ :=
  if h : source.2 = row.1.1 then
    G.scaledMixedCandidateAtomUse proposal edgeLabel qLaw R
      n scale rho omega source.1 row.1
      (by
        have hcolor : (source.2, row.1.2) = row.1 := by
          apply Prod.ext
          · exact h
          · rfl
        exact hcolor ▸ G.decodeMixedGraphAtom
          (G.mixedBlockProposal proposal source.2) edgeLabel
          (G.mixedBlockLaw qLaw source.2)
          (G.mixedBlockRealization proposal edgeLabel qLaw R source.2)
          source.1 state row.1.2) row.2
  else 0

theorem mixedBlockCandidateUse_nonneg
    (n : ℕ) (scale rho omega : ℝ)
    (huse0 : ∀ v c z row,
      0 ≤ G.scaledMixedCandidateAtomUse proposal edgeLabel qLaw R
        n scale rho omega v c z row)
    (source : G.V × Fin B)
    (state : G.MixedGraphPackedBlockState
      proposal edgeLabel qLaw R source.2)
    (row : G.MixedBlockCapacityRow proposal edgeLabel qLaw R) :
    0 ≤ G.mixedBlockCandidateUse proposal edgeLabel qLaw R
      n scale rho omega source state row := by
  unfold mixedBlockCandidateUse
  split
  · exact huse0 _ _ _ _
  · exact le_rfl

theorem mixedBlockCandidateUse_le_one
    (n : ℕ) (scale rho omega : ℝ)
    (huse1 : ∀ v c z row,
      G.scaledMixedCandidateAtomUse proposal edgeLabel qLaw R
        n scale rho omega v c z row ≤ 1)
    (source : G.V × Fin B)
    (state : G.MixedGraphPackedBlockState
      proposal edgeLabel qLaw R source.2)
    (row : G.MixedBlockCapacityRow proposal edgeLabel qLaw R) :
    G.mixedBlockCandidateUse proposal edgeLabel qLaw R
      n scale rho omega source state row ≤ 1 := by
  unfold mixedBlockCandidateUse
  split
  · exact huse1 _ _ _ _
  · norm_num

theorem mixedBlockCandidate_rowMean_eq
    (n : ℕ) (scale rho omega : ℝ)
    (row : G.MixedBlockCapacityRow proposal edgeLabel qLaw R) :
    FiniteCategoricalSelection.rowMean
        (fun source : G.V × Fin B ↦
          G.mixedBlockProbability proposal edgeLabel qLaw R
            omega source.1 source.2)
        (G.mixedBlockCandidateUse proposal edgeLabel qLaw R
          n scale rho omega) row =
      ∑ v : G.V,
        ∑ z : G.MixedGraphAtom proposal edgeLabel qLaw R v row.1,
          G.smoothedMixedGraphProbability proposal edgeLabel qLaw R
            omega v row.1 z *
          G.scaledMixedCandidateAtomUse proposal edgeLabel qLaw R
            n scale rho omega v row.1 z row.2 := by
  classical
  unfold FiniteCategoricalSelection.rowMean
  rw [Fintype.sum_prod_type]
  rw [Finset.sum_comm]
  rw [Finset.sum_eq_single row.1.1]
  · apply Finset.sum_congr rfl
    intro v _
    simp only [mixedBlockCandidateUse, dite_true]
    simpa [mixedBlockProbability, mixedBlockProposal, mixedBlockLaw,
      mixedBlockRealization] using
      (Subtwo.sum_paddedLabelledProbability_mul_decode_coordinate
        (fun v i ↦ G.MixedGraphAtom
          (G.mixedBlockProposal proposal row.1.1) edgeLabel
          (G.mixedBlockLaw qLaw row.1.1)
          (G.mixedBlockRealization proposal edgeLabel qLaw R row.1.1) v i)
        (fun _ _ ↦ none)
        (mixedGraphAtomBound (Label := Label)
          (β := β) (qstep := qstep) (r := r))
        (fun v i ↦ G.mixedGraphAtom_card_le
          (G.mixedBlockProposal proposal row.1.1) edgeLabel
          (G.mixedBlockLaw qLaw row.1.1)
          (G.mixedBlockRealization proposal edgeLabel qLaw R row.1.1) v i)
        (G.smoothedMixedGraphProbability
          (G.mixedBlockProposal proposal row.1.1) edgeLabel
          (G.mixedBlockLaw qLaw row.1.1)
          (G.mixedBlockRealization proposal edgeLabel qLaw R row.1.1) omega)
        (fun v i ↦ G.sum_smoothedMixedGraphProbability
          (G.mixedBlockProposal proposal row.1.1) edgeLabel
          (G.mixedBlockLaw qLaw row.1.1)
          (G.mixedBlockRealization proposal edgeLabel qLaw R row.1.1) omega v i)
        v row.1.2 (fun z ↦ G.scaledMixedCandidateAtomUse
          proposal edgeLabel qLaw R n scale rho omega v row.1 z row.2))
  · intro b _ hb
    simp [mixedBlockCandidateUse, hb]
  · simp

theorem sum_mixedBlockCandidateUse_le_weightedColumn
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
    (source : G.V × Fin B)
    (state : G.MixedGraphPackedBlockState
      proposal edgeLabel qLaw R source.2) :
    (∑ row : G.MixedBlockCapacityRow proposal edgeLabel qLaw R,
      G.mixedBlockCandidateUse proposal edgeLabel qLaw R n
        ((L : ℝ) * mixedCandidateOrientedScale (Label := Label)
          (β := β) (qstep := qstep) (r := r) rho s omega C0)
        rho omega source state row) ≤
      (k : ℝ) * mixedCandidateWeightedPerColorColumnBound
        (Label := Label) (β := β) (qstep := qstep) (r := r) n := by
  classical
  rw [Fintype.sum_sigma]
  simp only [mixedBlockCandidateUse]
  calc
    _ = ∑ i : Fin k,
        ∑ row : G.MixedCandidateRowAt proposal edgeLabel qLaw R
          (source.2, i),
        G.scaledMixedCandidateAtomUse proposal edgeLabel qLaw R n
          ((L : ℝ) * mixedCandidateOrientedScale (Label := Label)
            (β := β) (qstep := qstep) (r := r) rho s omega C0)
          rho omega source.1 (source.2, i)
          (G.decodeMixedGraphAtom
            (G.mixedBlockProposal proposal source.2) edgeLabel
            (G.mixedBlockLaw qLaw source.2)
            (G.mixedBlockRealization proposal edgeLabel qLaw R source.2)
            source.1 state i) row := by
      rw [Fintype.sum_prod_type]
      simp
    _ ≤ ∑ _i : Fin k,
        mixedCandidateWeightedPerColorColumnBound
          (Label := Label) (β := β) (qstep := qstep) (r := r) n := by
      apply Finset.sum_le_sum
      intro i _
      exact G.sum_scaledMixedCandidateAtomUse_mul_le_weightedColumn
        proposal edgeLabel qLaw R hL hn hq0 hqmarg hqsingle hqsum
        hs hqstep hr0 hleft homega0 homega1 hrho hC0
        hproposal0 hproposal hstar source.1 (source.2, i)
        (G.decodeMixedGraphAtom
          (G.mixedBlockProposal proposal source.2) edgeLabel
          (G.mixedBlockLaw qLaw source.2)
          (G.mixedBlockRealization proposal edgeLabel qLaw R source.2)
          source.1 state i)
    _ = _ := by simp

end WeightedMultigraph

end
end WeightedEdgeColoring
