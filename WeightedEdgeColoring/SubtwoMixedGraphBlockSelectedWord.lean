import WeightedEdgeColoring.SubtwoMixedGraphBlockDeviationAsymptotic

/-! Physical full-word decoding with the retained endpoint-label charge. -/

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

theorem selectedMixedBlockLabelCount_eq_fullWord
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
    (v : G.V) (label : Label) :
    G.selectedMixedBlockLabelCount proposal edgeLabel qLaw R
      choice v label =
    ∑ c : Fin B × Fin k,
      if G.mixedGraphAtomLabel proposal edgeLabel qLaw R
        v c (selected v c) = some label then (1 : ℝ) else 0 := by
  classical
  unfold selectedMixedBlockLabelCount
  rw [Fintype.sum_prod_type]
  apply Finset.sum_congr rfl
  intro b _
  apply Finset.sum_congr rfl
  intro i _
  rw [← hencode v b]
  simp only [decodeMixedGraphLabel, G.decode_encodeMixedGraphWord]
  rfl

theorem exists_mixedGraphFullWord_with_blockLabelCharge
    (hk : 0 < k)
    (hq0 : ∀ v c S, 0 ≤ qLaw v c S)
    (hqsum : ∀ v c, ∑ S, qLaw v c S = 1)
    (hqsingle : ∀ v c S, qLaw v c S ≠ 0 → S ≠ ∅ →
      ∃ label : Label, ∀ f ∈ S, edgeLabel v f = label)
    (hs : 0 ≤ s) (hqstep : 0 ≤ qstep) (hr0 : 0 ≤ r)
    (hleft : 0 ≤ 1 - s * (1 + qstep + r))
    (homega0 : 0 < omega) (homega1 : omega ≤ 1)
    (n : ℕ) (candidateScale rho pairScale selfScale deviation : ℝ)
    (choice : ∀ v : G.V, ∀ b : Fin B,
      G.MixedGraphPackedBlockState proposal edgeLabel qLaw R b)
    (hsupport : ∀ v b,
      0 < G.mixedBlockProbability proposal edgeLabel qLaw R
        omega v b (choice v b))
    (hrows : ∀ row : G.MixedBlockJointRow proposal edgeLabel qLaw R,
      FiniteCategoricalSelection.rowLoad
        (G.mixedBlockJointUse proposal edgeLabel qLaw R
          n candidateScale rho omega pairScale selfScale) row
        (fun source ↦ choice source.1 source.2) <
      FiniteCategoricalSelection.rowMean
        (fun source : G.V × Fin B ↦
          G.mixedBlockProbability proposal edgeLabel qLaw R
            omega source.1 source.2)
        (G.mixedBlockJointUse proposal edgeLabel qLaw R
          n candidateScale rho omega pairScale selfScale) row +
        deviation) :
    ∃ selected : ∀ v : G.V, ∀ c : Fin B × Fin k,
        G.MixedGraphAtom proposal edgeLabel qLaw R v c,
      (∀ v b,
        G.encodeMixedGraphWord
          (G.mixedBlockProposal proposal b) edgeLabel
          (G.mixedBlockLaw qLaw b)
          (G.mixedBlockRealization proposal edgeLabel qLaw R b)
          v (fun i ↦ selected v (b, i)) = choice v b) ∧
      ∀ v label,
        (∑ c : Fin B × Fin k,
          if G.mixedGraphAtomLabel proposal edgeLabel qLaw R
            v c (selected v c) = some label then (1 : ℝ) else 0) <
        (∑ c : Fin B × Fin k,
          subsetLabelMass (edgeLabel v) (qLaw v c) label) +
        ((B : ℝ) * k) * omega + (k : ℝ) * deviation := by
  classical
  obtain ⟨selected, hencode⟩ :=
    G.exists_mixedGraphFullWord_of_supported_blocks
      proposal edgeLabel qLaw R hq0 hqsum hqsingle
      hs hqstep hr0 hleft homega0 homega1 choice hsupport
  refine ⟨selected, hencode, ?_⟩
  intro v label
  rw [← G.selectedMixedBlockLabelCount_eq_fullWord
    proposal edgeLabel qLaw R choice selected hencode v label]
  exact G.selectedMixedBlockLabelCount_lt_charge
    proposal edgeLabel qLaw R hk n candidateScale rho omega
    pairScale selfScale deviation hq0 homega0.le homega1
    choice v label (hrows (Sum.inr (v, some label)))

end WeightedMultigraph

end
end WeightedEdgeColoring
