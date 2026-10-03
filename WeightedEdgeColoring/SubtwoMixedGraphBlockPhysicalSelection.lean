import WeightedEdgeColoring.SubtwoMixedGraphBlockResidualPhysical

/-! A selected block word supplies all physical decoder inputs at once. -/

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

theorem selectedMixedEndpointLabelCount_encode_eq_atomSum
    (selected : ∀ v : G.V, ∀ c : Fin B × Fin k,
      G.MixedGraphAtom proposal edgeLabel qLaw R v c)
    (v : G.V) (label : Label) :
    G.selectedMixedEndpointLabelCount proposal edgeLabel qLaw R
      (fun w ↦ G.encodeMixedGraphWord proposal edgeLabel qLaw R
        w (selected w)) v label =
    ∑ c : Fin B × Fin k,
      if G.mixedGraphAtomLabel proposal edgeLabel qLaw R
        v c (selected v c) = some label then (1 : ℝ) else 0 := by
  classical
  unfold selectedMixedEndpointLabelCount
  apply Finset.sum_congr rfl
  intro c _
  simp [decodeMixedGraphLabel]

theorem exists_fullMixedWord_of_selectedBlocks
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
    (hsupport : ∀ v b,
      0 < G.mixedBlockProbability proposal edgeLabel qLaw R
        omega v b (choice v b))
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
          n scale rho omega pairScale selfScale) row + deviation)
    (residualBound : G.V → ℝ)
    (hblockResidual : ∀ v,
      (∑ e : G.StarEdge v, G.weight e.1 *
        (1 - min 1 (G.selectedMixedBlockTotalOptionMass
          proposal edgeLabel qLaw R rho omega choice e.1))) ≤
        residualBound v) :
    ∃ selected : ∀ v : G.V, ∀ c : Fin B × Fin k,
        G.MixedGraphAtom proposal edgeLabel qLaw R v c,
      let fullChoice : ∀ v : G.V,
          G.MixedGraphPackedState proposal edgeLabel qLaw R :=
        fun v ↦ G.encodeMixedGraphWord proposal edgeLabel qLaw R
          v (selected v)
      (∀ c (row : G.MixedCandidateRowAt proposal edgeLabel qLaw R c),
        G.selectedMixedCandidateCapacityLoad
          proposal edgeLabel qLaw R rho omega fullChoice c row <
          rho / (1 - omega) + scale / (n : ℝ) * deviation) ∧
      (∀ v c,
        G.selectedMixedNormalizedTinyReservoirLoad
          proposal edgeLabel qLaw R rho omega fullChoice v c <
        rho / (1 - omega) *
          G.selectedMixedConcreteReservoirSize
            proposal edgeLabel qLaw R fullChoice v c +
          scale / (n : ℝ) * deviation) ∧
      (∀ v label,
        G.selectedMixedEndpointLabelCount
          proposal edgeLabel qLaw R fullChoice v label <
        (∑ c : Fin B × Fin k,
          subsetLabelMass (edgeLabel v) (qLaw v c) label) +
        ((B : ℝ) * k) * omega + (k : ℝ) * deviation) ∧
      (∀ v,
        G.weightedResidualStar
          (G.selectedMixedResidualOptionMass
            proposal edgeLabel qLaw R rho omega fullChoice) v ≤
          residualBound v) := by
  classical
  obtain ⟨selected, hencode, hlabels⟩ :=
    G.exists_mixedGraphFullWord_with_blockLabelCharge
      proposal edgeLabel qLaw R hk hq0 hqsum hqsingle
      hs hqstep hr0 hleft homega0 homega1.le
      n scale rho pairScale selfScale deviation choice hsupport hrows
  refine ⟨selected, ?_, ?_, ?_, ?_⟩
  · exact G.mixedBlockFullCandidateCapacity_lt
      proposal edgeLabel qLaw R hB hk hn scale rho omega
      pairScale selfScale deviation hscale
      hq0 hqmarg hqsingle hqsum hs hqstep hr0 hleft
      homega0 homega1 hrho choice selected hencode hrows
  · exact G.mixedBlockFullTinyReservoir_lt_relative
      proposal edgeLabel qLaw R hB hk hn scale rho omega
      pairScale selfScale deviation hscale
      hq0 hqmarg hqsingle hqsum hs hqstep hr0 hleft
      homega0 homega1 hrho hproposal0 choice selected hencode hrows
  · intro v label
    rw [G.selectedMixedEndpointLabelCount_encode_eq_atomSum
      proposal edgeLabel qLaw R selected v label]
    exact hlabels v label
  · intro v
    rw [weightedSelectedMixedResidualStar_eq_blockClippedStar
      (G := G) proposal edgeLabel qLaw R rho omega
      choice selected hencode v]
    exact hblockResidual v

end WeightedMultigraph

end
end WeightedEdgeColoring
