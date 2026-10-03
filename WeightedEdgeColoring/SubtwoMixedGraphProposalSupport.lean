import WeightedEdgeColoring.SubtwoMixedGraphSelectedNormalization

/-! A positive decoded option retains positive physical proposal support. -/

namespace WeightedEdgeColoring
noncomputable section

private theorem pairedOption_source_pos
    {PU PV IU IV : Type*}
    (rho y : ℝ) (lambdaU : PU → ℝ) (lambdaV : PV → ℝ)
    (aU : PU → IU → ℝ) (aV : PV → IV → ℝ)
    (p : PU) (q : PV) (i : IU) (j : IV)
    (hy0 : 0 ≤ y)
    (hpos : 0 < pairedOption rho y lambdaU lambdaV aU aV p q i j) :
    0 < y := by
  by_contra hnot
  have hzero : y = 0 := le_antisymm (le_of_not_gt hnot) hy0
  simp [pairedOption, hzero] at hpos

namespace WeightedMultigraph
universe u
variable (G : WeightedMultigraph.{u})
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

theorem positive_selectedMixedNormalizedLargeOptionMass_proposal
    (hs : 0 ≤ s) (hproposal0 : ∀ e c, 0 ≤ proposal e c)
    (rho omega : ℝ)
    (choice : ∀ v : G.V,
      G.MixedGraphPackedState proposal edgeLabel qLaw R)
    (e : G.E) (c : Color)
    (i j : Fin (explicitLargeSlotBound β qstep r))
    (hpos : 0 < G.selectedMixedNormalizedLargeOptionMass
      proposal edgeLabel qLaw R rho omega choice e c i j) :
    0 < proposal e c := by
  have hp := (G.selectedMixedNormalizedLargeOptionMass_pos_iff
    proposal edgeLabel qLaw R rho omega choice e c i j).mp hpos
  unfold selectedMixedLargeOptionMass mixedGraphLargeProductMass at hp
  have hy0 : 0 ≤ G.mixedGraphLargeEdgeMass proposal s β e c := by
    unfold mixedGraphLargeEdgeMass
    split
    · exact mul_nonneg hs (hproposal0 e c)
    · exact le_refl _
  have hy := pairedOption_source_pos rho
    (G.mixedGraphLargeEdgeMass proposal s β e c) _ _ _ _ _ _ i j hy0 hp
  unfold mixedGraphLargeEdgeMass at hy
  split at hy
  · rcases mul_pos_iff.mp hy with h | h
    · exact h.2
    · exact (not_lt_of_ge hs h.1).elim
  · exact (not_lt_of_ge (le_refl (0:ℝ)) hy).elim

theorem positive_selectedMixedNormalizedTinyOptionMass_proposal
    (hs : 0 ≤ s) (hproposal0 : ∀ e c, 0 ≤ proposal e c)
    (rho omega : ℝ)
    (choice : ∀ v : G.V,
      G.MixedGraphPackedState proposal edgeLabel qLaw R)
    (e : G.E) (c : Color)
    (hpos : 0 < G.selectedMixedNormalizedTinyOptionMass
      proposal edgeLabel qLaw R rho omega choice e c) :
    0 < proposal e c := by
  have hp := (G.selectedMixedNormalizedTinyOptionMass_pos_iff
    proposal edgeLabel qLaw R rho omega choice e c).mp hpos
  unfold selectedMixedTinyOptionMass mixedGraphTinyProductMass at hp
  have hy0 : 0 ≤ G.mixedGraphTinyEdgeMass proposal s β e c := by
    unfold mixedGraphTinyEdgeMass
    split
    · exact mul_nonneg hs (hproposal0 e c)
    · exact le_refl _
  have hy := pairedOption_source_pos rho
    (G.mixedGraphTinyEdgeMass proposal s β e c) _ _ _ _ _ _ 0 0 hy0 hp
  unfold mixedGraphTinyEdgeMass at hy
  split at hy
  · rcases mul_pos_iff.mp hy with h | h
    · exact h.2
    · exact (not_lt_of_ge hs h.1).elim
  · exact (not_lt_of_ge (le_refl (0:ℝ)) hy).elim

end WeightedMultigraph
end
end WeightedEdgeColoring
