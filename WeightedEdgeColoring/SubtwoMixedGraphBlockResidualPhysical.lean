import WeightedEdgeColoring.SubtwoMixedGraphBlockFullRows
import WeightedEdgeColoring.SubtwoMixedGraphFeasibleRelativeDecoder

/-! The dyadic decoder's two residual terms are supported on the same
clipped full-word residual controlled by the block-variance selector. -/

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

theorem tinyResidualLossLoad_selectedMixed_le_fullStar
    (rho omega : ℝ)
    (choice : ∀ v : G.V,
      G.MixedGraphPackedState proposal edgeLabel qLaw R)
    (v : G.V) :
    G.tinyResidualLossLoad (G.selectedMixedTinyEdges (β := β))
        (fun e ↦ G.selectedMixedResidualOptionMass
          proposal edgeLabel qLaw R rho omega choice e.1) v ≤
      G.weightedResidualStar
        (G.selectedMixedResidualOptionMass
          proposal edgeLabel qLaw R rho omega choice) v := by
  classical
  unfold tinyResidualLossLoad weightedResidualStar
  have hsub := Finset.sum_subtype
    (p := fun e : G.E ↦ e ∈ G.selectedMixedTinyEdges (β := β))
    (F := Finset.Subtype.fintype (G.selectedMixedTinyEdges (β := β)))
    (G.selectedMixedTinyEdges (β := β)) (by intro e; simp)
    (fun e ↦ if G.Inc v e then
      G.selectedMixedResidualOptionMass
        proposal edgeLabel qLaw R rho omega choice e * G.weight e else 0)
  rw [← hsub]
  apply Finset.sum_le_univ_sum_of_nonneg
  intro e
  by_cases hinc : G.Inc v e
  · simp only [if_pos hinc]
    exact mul_nonneg
      (G.selectedMixedResidualOptionMass_nonneg
        proposal edgeLabel qLaw R rho omega choice e)
      (G.weight_nonneg e)
  · simp [hinc]

theorem weightedSelectedMixedLargeResidual_le_fullStar
    (rho omega : ℝ)
    (choice : ∀ v : G.V,
      G.MixedGraphPackedState proposal edgeLabel qLaw R)
    (v : G.V) :
    G.weightedResidualStar
        (G.selectedMixedLargeResidual
          proposal edgeLabel qLaw R rho omega choice) v ≤
      G.weightedResidualStar
        (G.selectedMixedResidualOptionMass
          proposal edgeLabel qLaw R rho omega choice) v := by
  classical
  unfold weightedResidualStar
  apply Finset.sum_le_sum
  intro e _
  by_cases hinc : G.Inc v e
  · simp only [if_pos hinc]
    unfold selectedMixedLargeResidual
    split
    · exact le_rfl
    · simpa using mul_nonneg
        (G.selectedMixedResidualOptionMass_nonneg
          proposal edgeLabel qLaw R rho omega choice e)
        (G.weight_nonneg e)
  · simp [hinc]

theorem weightedSelectedMixedResidualStar_eq_blockClippedStar
    {B k : ℕ}
    (proposal : G.E → (Fin B × Fin k) → ℝ)
    (edgeLabel : ∀ v : G.V, G.StarEdge v → Label)
    (qLaw : ∀ v : G.V, (Fin B × Fin k) →
      Finset (G.StarEdge v) → ℝ)
    (R : ∀ v c label,
      G.BoundedProfileRealization
        (G.conditionalEndpointProposal (edgeLabel v)
          (fun e : G.StarEdge v ↦ proposal e.1 c) (qLaw v c) label)
        s β qstep r hβ hr)
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
    (v : G.V) :
    G.weightedResidualStar
        (G.selectedMixedResidualOptionMass
          proposal edgeLabel qLaw R rho omega
          (fun w ↦ G.encodeMixedGraphWord proposal edgeLabel qLaw R
            w (selected w))) v =
      ∑ e : G.StarEdge v, G.weight e.1 *
        (1 - min 1 (G.selectedMixedBlockTotalOptionMass
          proposal edgeLabel qLaw R rho omega choice e.1)) := by
  classical
  unfold weightedResidualStar selectedMixedResidualOptionMass
  calc
    (∑ e : G.E, if G.Inc v e then
        (1 - min 1 (G.selectedMixedAllOptionMass
          proposal edgeLabel qLaw R rho omega
          (fun w ↦ G.encodeMixedGraphWord proposal edgeLabel qLaw R
            w (selected w)) e)) * G.weight e else 0) =
      ∑ e : G.StarEdge v,
        (1 - min 1 (G.selectedMixedAllOptionMass
          proposal edgeLabel qLaw R rho omega
          (fun w ↦ G.encodeMixedGraphWord proposal edgeLabel qLaw R
            w (selected w)) e.1)) * G.weight e.1 := by
        rw [← Finset.sum_filter]
        exact Finset.sum_subtype (Finset.univ.filter (G.Inc v))
          (by intro e; simp)
          (fun e ↦ (1 - min 1 (G.selectedMixedAllOptionMass
            proposal edgeLabel qLaw R rho omega
            (fun w ↦ G.encodeMixedGraphWord proposal edgeLabel qLaw R
              w (selected w)) e)) * G.weight e)
    _ = _ := by
      apply Finset.sum_congr rfl
      intro e _
      rw [← G.selectedMixedBlockTotalOptionMass_eq_fullWord
        proposal edgeLabel qLaw R rho omega choice selected hencode e.1]
      ring

end WeightedMultigraph

end
end WeightedEdgeColoring
