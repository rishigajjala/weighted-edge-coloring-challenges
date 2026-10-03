import WeightedEdgeColoring.SubtwoMixedGraphBlockResidualScalars
import WeightedEdgeColoring.SubtwoMixedGraphJointDecoder
import WeightedEdgeColoring.SubtwoMixedGraphSelectedNormalization
import WeightedEdgeColoring.SubtwoMixedGraphReservoirSelector

/-! Transport fixed-block candidate rows to the physically encoded full word. -/

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

theorem mixedBlockCandidate_rowLoad_eq_fullWord
    (hB : 0 < B) (hk : 0 < k)
    (n : ℕ) (scale rho omega : ℝ)
    (choice : ∀ v : G.V, ∀ b : Fin B,
      G.MixedGraphPackedBlockState proposal edgeLabel qLaw R b)
    (selected : ∀ v : G.V, ∀ c : Fin B × Fin k,
      G.MixedGraphAtom proposal edgeLabel qLaw R v c)
    (hencode : ∀ v b,
      G.encodeMixedGraphWord
        (G.mixedBlockProposal proposal b) edgeLabel
        (G.mixedBlockLaw qLaw b)
        (G.mixedBlockRealization proposal edgeLabel qLaw R b)
        v (fun i ↦ selected v (b, i)) = choice v b)
    (row : G.MixedBlockCapacityRow proposal edgeLabel qLaw R) :
    FiniteCategoricalSelection.rowLoad
      (G.mixedBlockCandidateUse proposal edgeLabel qLaw R
        n scale rho omega) row
      (fun source ↦ choice source.1 source.2) =
    FiniteCategoricalSelection.rowLoad
      (G.mixedGraphJointUse proposal edgeLabel qLaw R
        (by simpa using Nat.mul_pos hB hk :
          0 < Fintype.card (Fin B × Fin k))
        n scale rho omega)
      (Sum.inl row)
      (fun v ↦ G.encodeMixedGraphWord proposal edgeLabel qLaw R
        v (selected v)) := by
  classical
  unfold FiniteCategoricalSelection.rowLoad
  rw [Fintype.sum_prod_type, Finset.sum_comm]
  rw [Finset.sum_eq_single row.1.1]
  · simp only [mixedBlockCandidateUse, mixedGraphJointUse,
      Finset.sum_congr]
    apply Finset.sum_congr rfl
    intro v _
    simp only [dite_true]
    rw [← hencode v row.1.1]
    simp
  · intro b _ hb
    simp [mixedBlockCandidateUse, hb]
  · simp

theorem mixedBlockCandidate_rowMean_eq_fullWord
    (hB : 0 < B) (hk : 0 < k)
    (n : ℕ) (scale rho omega : ℝ)
    (row : G.MixedBlockCapacityRow proposal edgeLabel qLaw R) :
    FiniteCategoricalSelection.rowMean
      (fun source : G.V × Fin B ↦
        G.mixedBlockProbability proposal edgeLabel qLaw R
          omega source.1 source.2)
      (G.mixedBlockCandidateUse proposal edgeLabel qLaw R
        n scale rho omega) row =
    FiniteCategoricalSelection.rowMean
      (G.paddedMixedGraphWordProbability
        proposal edgeLabel qLaw R omega)
      (G.mixedGraphJointUse proposal edgeLabel qLaw R
        (by simpa using Nat.mul_pos hB hk :
          0 < Fintype.card (Fin B × Fin k))
        n scale rho omega)
      (Sum.inl row) := by
  classical
  rw [G.mixedBlockCandidate_rowMean_eq]
  change (∑ v : G.V,
      ∑ z : G.MixedGraphAtom proposal edgeLabel qLaw R v row.1,
        G.smoothedMixedGraphProbability proposal edgeLabel qLaw R
          omega v row.1 z *
        G.scaledMixedCandidateAtomUse proposal edgeLabel qLaw R
          n scale rho omega v row.1 z row.2) =
    ∑ v : G.V,
      ∑ packed : G.MixedGraphPackedState proposal edgeLabel qLaw R,
        G.paddedMixedGraphWordProbability
          proposal edgeLabel qLaw R omega v packed *
        G.scaledMixedCandidateAtomUse proposal edgeLabel qLaw R
          n scale rho omega v row.1
          (G.decodeMixedGraphAtom proposal edgeLabel qLaw R
            v packed row.1) row.2
  apply Finset.sum_congr rfl
  intro v _
  exact (Subtwo.sum_paddedLabelledProbability_mul_decode_coordinate
    (fun v c ↦ G.MixedGraphAtom proposal edgeLabel qLaw R v c)
    (fun _ _ ↦ none)
    (mixedGraphAtomBound (Label := Label)
      (β := β) (qstep := qstep) (r := r))
    (fun v c ↦ G.mixedGraphAtom_card_le
      proposal edgeLabel qLaw R v c)
    (G.smoothedMixedGraphProbability proposal edgeLabel qLaw R omega)
    (fun v c ↦ G.sum_smoothedMixedGraphProbability
      proposal edgeLabel qLaw R omega v c)
    v row.1 (fun z ↦ G.scaledMixedCandidateAtomUse
      proposal edgeLabel qLaw R n scale rho omega v row.1 z row.2)).symm

theorem mixedBlockJointCandidateRows_transfer
    (hB : 0 < B) (hk : 0 < k)
    (n : ℕ) (scale rho omega pairScale selfScale deviation : ℝ)
    (choice : ∀ v : G.V, ∀ b : Fin B,
      G.MixedGraphPackedBlockState proposal edgeLabel qLaw R b)
    (selected : ∀ v : G.V, ∀ c : Fin B × Fin k,
      G.MixedGraphAtom proposal edgeLabel qLaw R v c)
    (hencode : ∀ v b,
      G.encodeMixedGraphWord
        (G.mixedBlockProposal proposal b) edgeLabel
        (G.mixedBlockLaw qLaw b)
        (G.mixedBlockRealization proposal edgeLabel qLaw R b)
        v (fun i ↦ selected v (b, i)) = choice v b)
    (hrows : ∀ row : G.MixedBlockJointRow proposal edgeLabel qLaw R,
      FiniteCategoricalSelection.rowLoad
        (G.mixedBlockJointUse proposal edgeLabel qLaw R
          n scale rho omega pairScale selfScale) row
        (fun source ↦ choice source.1 source.2) <
      FiniteCategoricalSelection.rowMean
        (fun source : G.V × Fin B ↦
          G.mixedBlockProbability proposal edgeLabel qLaw R
            omega source.1 source.2)
        (G.mixedBlockJointUse proposal edgeLabel qLaw R
          n scale rho omega pairScale selfScale) row + deviation) :
    ∀ row : G.MixedBlockCapacityRow proposal edgeLabel qLaw R,
      FiniteCategoricalSelection.rowLoad
        (G.mixedGraphJointUse proposal edgeLabel qLaw R
          (by simpa using Nat.mul_pos hB hk :
            0 < Fintype.card (Fin B × Fin k))
          n scale rho omega)
        (Sum.inl row)
        (fun v ↦ G.encodeMixedGraphWord proposal edgeLabel qLaw R
          v (selected v)) <
      FiniteCategoricalSelection.rowMean
        (G.paddedMixedGraphWordProbability
          proposal edgeLabel qLaw R omega)
        (G.mixedGraphJointUse proposal edgeLabel qLaw R
          (by simpa using Nat.mul_pos hB hk :
            0 < Fintype.card (Fin B × Fin k))
          n scale rho omega)
        (Sum.inl row) + deviation := by
  intro row
  have h := hrows (Sum.inl (Sum.inl row))
  change FiniteCategoricalSelection.rowLoad
      (G.mixedBlockCandidateUse proposal edgeLabel qLaw R
        n scale rho omega) row
      (fun source ↦ choice source.1 source.2) <
    FiniteCategoricalSelection.rowMean
      (fun source : G.V × Fin B ↦
        G.mixedBlockProbability proposal edgeLabel qLaw R
          omega source.1 source.2)
      (G.mixedBlockCandidateUse proposal edgeLabel qLaw R
        n scale rho omega) row + deviation at h
  rw [G.mixedBlockCandidate_rowLoad_eq_fullWord
    proposal edgeLabel qLaw R hB hk n scale rho omega
      choice selected hencode row,
    G.mixedBlockCandidate_rowMean_eq_fullWord
      proposal edgeLabel qLaw R hB hk n scale rho omega row] at h
  exact h

theorem selectedMixedBlockTotalOptionMass_eq_fullWord
    (rho omega : ℝ)
    (choice : ∀ v : G.V, ∀ b : Fin B,
      G.MixedGraphPackedBlockState proposal edgeLabel qLaw R b)
    (selected : ∀ v : G.V, ∀ c : Fin B × Fin k,
      G.MixedGraphAtom proposal edgeLabel qLaw R v c)
    (hencode : ∀ v b,
      G.encodeMixedGraphWord
        (G.mixedBlockProposal proposal b) edgeLabel
        (G.mixedBlockLaw qLaw b)
        (G.mixedBlockRealization proposal edgeLabel qLaw R b)
        v (fun i ↦ selected v (b, i)) = choice v b)
    (e : G.E) :
    G.selectedMixedBlockTotalOptionMass
      proposal edgeLabel qLaw R rho omega choice e =
    G.selectedMixedAllOptionMass
      proposal edgeLabel qLaw R rho omega
      (fun v ↦ G.encodeMixedGraphWord proposal edgeLabel qLaw R
        v (selected v)) e := by
  classical
  unfold selectedMixedBlockTotalOptionMass selectedMixedAllOptionMass
  rw [Fintype.sum_prod_type]
  apply Finset.sum_congr rfl
  intro b _
  unfold mixedBlockOptionMass
  apply Finset.sum_congr rfl
  intro i _
  rw [← hencode (G.fst e) b, ← hencode (G.snd e) b]
  simp [mixedGraphCoordinateOptionMass,
    selectedMixedLargeOptionMass, selectedMixedTinyOptionMass,
    mixedBlockProposal, mixedBlockLaw, mixedBlockRealization]
  rfl

theorem mixedBlockFullCandidateCapacity_lt
    (hB : 0 < B) (hk : 0 < k) {n : ℕ} (hn : 0 < n)
    (scale rho omega pairScale selfScale deviation : ℝ)
    (hscale : 0 < scale)
    (hq0 : ∀ v c S, 0 ≤ qLaw v c S)
    (hqmarg : ∀ v c (f : G.StarEdge v),
      (∑ S, if f ∈ S then qLaw v c S else 0) = proposal f.1 c)
    (hqsingle : ∀ v c S, qLaw v c S ≠ 0 → S ≠ ∅ →
      ∃ label : Label, ∀ f ∈ S, edgeLabel v f = label)
    (hqsum : ∀ v c, ∑ S, qLaw v c S = 1)
    (hs : 0 ≤ s) (hqstep : 0 ≤ qstep) (hr0 : 0 ≤ r)
    (hleft : 0 ≤ 1 - s * (1 + qstep + r))
    (homega0 : 0 < omega) (homega1 : omega < 1)
    (hrho : 0 ≤ rho)
    (choice : ∀ v : G.V, ∀ b : Fin B,
      G.MixedGraphPackedBlockState proposal edgeLabel qLaw R b)
    (selected : ∀ v : G.V, ∀ c : Fin B × Fin k,
      G.MixedGraphAtom proposal edgeLabel qLaw R v c)
    (hencode : ∀ v b,
      G.encodeMixedGraphWord
        (G.mixedBlockProposal proposal b) edgeLabel
        (G.mixedBlockLaw qLaw b)
        (G.mixedBlockRealization proposal edgeLabel qLaw R b)
        v (fun i ↦ selected v (b, i)) = choice v b)
    (hrows : ∀ row : G.MixedBlockJointRow proposal edgeLabel qLaw R,
      FiniteCategoricalSelection.rowLoad
        (G.mixedBlockJointUse proposal edgeLabel qLaw R
          n scale rho omega pairScale selfScale) row
        (fun source ↦ choice source.1 source.2) <
      FiniteCategoricalSelection.rowMean
        (fun source : G.V × Fin B ↦
          G.mixedBlockProbability proposal edgeLabel qLaw R
            omega source.1 source.2)
        (G.mixedBlockJointUse proposal edgeLabel qLaw R
          n scale rho omega pairScale selfScale) row + deviation) :
    ∀ c (row : G.MixedCandidateRowAt proposal edgeLabel qLaw R c),
      G.selectedMixedCandidateCapacityLoad
        proposal edgeLabel qLaw R rho omega
        (fun v ↦ G.encodeMixedGraphWord proposal edgeLabel qLaw R
          v (selected v)) c row <
        rho / (1 - omega) + scale / (n : ℝ) * deviation := by
  intro c row
  have hfull := G.mixedBlockJointCandidateRows_transfer
    proposal edgeLabel qLaw R hB hk n scale rho omega
    pairScale selfScale deviation choice selected hencode hrows ⟨c, row⟩
  have hmean := G.mixedGraphCandidateCapacity_rowMean_le
    proposal edgeLabel qLaw R
    (by simpa using Nat.mul_pos hB hk :
      0 < Fintype.card (Fin B × Fin k))
    n scale rho omega hq0 hqmarg hqsingle hqsum
    hs hqstep hr0 hleft homega0 homega1 hrho hscale ⟨c, row⟩
  have hbound := lt_of_lt_of_le hfull (add_le_add hmean le_rfl)
  change (∑ source : G.V,
      G.scaledMixedCandidateAtomUse proposal edgeLabel qLaw R
        n scale rho omega source c
        (G.decodeMixedGraphAtom proposal edgeLabel qLaw R source
          (G.encodeMixedGraphWord proposal edgeLabel qLaw R
            source (selected source)) c) row) <
      (n : ℝ) * (rho / (1 - omega)) / scale + deviation at hbound
  exact G.selectedMixedCandidateCapacityLoad_lt
    proposal edgeLabel qLaw R hn scale rho omega deviation hscale
    (fun v ↦ G.encodeMixedGraphWord proposal edgeLabel qLaw R
      v (selected v)) c row hbound

theorem mixedBlockFullTinyReservoir_lt_relative
    (hB : 0 < B) (hk : 0 < k) {n : ℕ} (hn : 0 < n)
    (scale rho omega pairScale selfScale deviation : ℝ)
    (hscale : 0 < scale)
    (hq0 : ∀ v c S, 0 ≤ qLaw v c S)
    (hqmarg : ∀ v c (f : G.StarEdge v),
      (∑ S, if f ∈ S then qLaw v c S else 0) = proposal f.1 c)
    (hqsingle : ∀ v c S, qLaw v c S ≠ 0 → S ≠ ∅ →
      ∃ label : Label, ∀ f ∈ S, edgeLabel v f = label)
    (hqsum : ∀ v c, ∑ S, qLaw v c S = 1)
    (hs : 0 ≤ s) (hqstep : 0 ≤ qstep) (hr0 : 0 ≤ r)
    (hleft : 0 ≤ 1 - s * (1 + qstep + r))
    (homega0 : 0 < omega) (homega1 : omega < 1)
    (hrho : 0 ≤ rho) (hproposal0 : ∀ e c, 0 ≤ proposal e c)
    (choice : ∀ v : G.V, ∀ b : Fin B,
      G.MixedGraphPackedBlockState proposal edgeLabel qLaw R b)
    (selected : ∀ v : G.V, ∀ c : Fin B × Fin k,
      G.MixedGraphAtom proposal edgeLabel qLaw R v c)
    (hencode : ∀ v b,
      G.encodeMixedGraphWord
        (G.mixedBlockProposal proposal b) edgeLabel
        (G.mixedBlockLaw qLaw b)
        (G.mixedBlockRealization proposal edgeLabel qLaw R b)
        v (fun i ↦ selected v (b, i)) = choice v b)
    (hrows : ∀ row : G.MixedBlockJointRow proposal edgeLabel qLaw R,
      FiniteCategoricalSelection.rowLoad
        (G.mixedBlockJointUse proposal edgeLabel qLaw R
          n scale rho omega pairScale selfScale) row
        (fun source ↦ choice source.1 source.2) <
      FiniteCategoricalSelection.rowMean
        (fun source : G.V × Fin B ↦
          G.mixedBlockProbability proposal edgeLabel qLaw R
            omega source.1 source.2)
        (G.mixedBlockJointUse proposal edgeLabel qLaw R
          n scale rho omega pairScale selfScale) row + deviation) :
    ∀ v c,
      G.selectedMixedNormalizedTinyReservoirLoad
          proposal edgeLabel qLaw R rho omega
          (fun v ↦ G.encodeMixedGraphWord proposal edgeLabel qLaw R
            v (selected v)) v c <
        rho / (1 - omega) *
          G.selectedMixedConcreteReservoirSize
            proposal edgeLabel qLaw R
            (fun v ↦ G.encodeMixedGraphWord proposal edgeLabel qLaw R
              v (selected v)) v c +
          scale / (n : ℝ) * deviation := by
  intro v c
  let fullChoice : ∀ v : G.V,
      G.MixedGraphPackedState proposal edgeLabel qLaw R :=
    fun v ↦ G.encodeMixedGraphWord proposal edgeLabel qLaw R
      v (selected v)
  have hfull := G.mixedBlockJointCandidateRows_transfer
    proposal edgeLabel qLaw R hB hk n scale rho omega
    pairScale selfScale deviation choice selected hencode hrows
    ⟨c, Sum.inr (G.selectedMixedTinyCandidateRow
      proposal edgeLabel qLaw R fullChoice v c)⟩
  exact G.selectedMixedNormalizedTinyReservoirLoad_lt_relative
    proposal edgeLabel qLaw R hn
    (by simpa using Nat.mul_pos hB hk :
      0 < Fintype.card (Fin B × Fin k))
    scale rho omega deviation hscale
    hq0 hqmarg hqsingle hqsum hs hqstep hr0 hleft
    homega0 homega1 hrho hproposal0 fullChoice v c hfull

end WeightedMultigraph

end
end WeightedEdgeColoring
