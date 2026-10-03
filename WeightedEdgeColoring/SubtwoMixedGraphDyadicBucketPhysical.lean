import WeightedEdgeColoring.SubtwoMixedGraphFeasibleRelativeDecoderSupport
import WeightedEdgeColoring.DyadicWeightUpperBounds

/-! Concrete finite bucket data for the support-sensitive mixed decoder. -/

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

theorem selectedMixedLargeResidual_dyadicBucket_data_of_cover
    (hβ1 : β ≤ 1) (L : ℕ)
    (hcover : 1 ≤ dyadicScale β L)
    (htop : dyadicScale β L < 2)
    (rho omega : ℝ)
    (choice : ∀ v : G.V,
      G.MixedGraphPackedState proposal edgeLabel qLaw R) :
    (∀ e, G.weight e ≤
      dyadicUpper β (dyadicBucket β L G.weight e)) ∧
    (∀ e, 0 < G.selectedMixedLargeResidual
        proposal edgeLabel qLaw R rho omega choice e →
      dyadicUpper β (dyadicBucket β L G.weight e) ≤
        2 * G.weight e) ∧
    (∑ h : Fin (L + 1), dyadicUpper β h) ≤ 4 := by
  refine ⟨?_, ?_, ?_⟩
  · intro e
    exact weight_le_dyadicUpper_bucket β L G.weight hcover
      (fun f _ ↦ G.weight_le_one f) (Finset.mem_univ e)
  · intro e he
    have hlarge : β ≤ G.weight e := by
      by_contra hnot
      have hsmall : ¬ β ≤ G.weight e := hnot
      simp [selectedMixedLargeResidual, hsmall] at he
    exact dyadicUpper_bucket_le_two_mul β L G.weight hβ hcover
      (fun f hf ↦ by
        have hfe : f = e := Finset.mem_singleton.mp hf
        subst f
        exact hlarge)
      (fun f _ ↦ G.weight_le_one f)
      (by simp : e ∈ ({e} : Finset G.E))
  · have hsum := sum_dyadicUpper_le_two_mul_top hβ.le L
    exact hsum.trans (by linarith)

theorem selectedMixedLargeResidual_dyadicBucket_data
    (hβ1 : β ≤ 1) (rho omega : ℝ)
    (choice : ∀ v : G.V,
      G.MixedGraphPackedState proposal edgeLabel qLaw R) :
    ∃ L : ℕ,
      1 ≤ dyadicScale β L ∧ dyadicScale β L < 2 ∧
      (∀ e, G.weight e ≤
        dyadicUpper β (dyadicBucket β L G.weight e)) ∧
      (∀ e, 0 < G.selectedMixedLargeResidual
          proposal edgeLabel qLaw R rho omega choice e →
        dyadicUpper β (dyadicBucket β L G.weight e) ≤
          2 * G.weight e) ∧
      (∑ h : Fin (L + 1), dyadicUpper β h) ≤ 4 := by
  obtain ⟨L, hcover, htop⟩ :=
    exists_dyadic_scale_mem_Ico_one_two β hβ hβ1
  exact ⟨L, hcover, htop,
    G.selectedMixedLargeResidual_dyadicBucket_data_of_cover
      proposal edgeLabel qLaw R hβ1 L hcover htop rho omega choice⟩

end WeightedMultigraph

end
end WeightedEdgeColoring
