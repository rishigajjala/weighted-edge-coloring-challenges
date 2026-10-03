import WeightedEdgeColoring.SubtwoDisjointBlockRestoration

/-! Join the actual boundary and internal partial colorings and add their local losses. -/

open scoped BigOperators
namespace WeightedEdgeColoring.Subtwo
noncomputable section
universe u

/-- Both losses are measured at the original vertex. The number of blocks
never enters this final same-palette assembly. -/
theorem exists_whole_partialColor_of_boundary_and_internal
    {G : WeightedEdgeColoring.WeightedMultigraph.{u}} {K : ℕ}
    (crossing internal B P : Finset G.E)
    (hpartition : crossing ∪ internal = Finset.univ)
    (hparts : Disjoint crossing internal)
    (hB : B ⊆ crossing) (hP : P ⊆ internal)
    (boundary inside : G.E → Fin K)
    (hboundary : G.IsFeasibleOn B boundary) (hinside : G.IsFeasibleOn P inside)
    (hseparate : ∀ e ∈ B, ∀ f ∈ P, ∀ v,
      G.Inc v e → G.Inc v f → boundary e ≠ inside f)
    (boundaryLoss internalLoss : ℝ)
    (hboundaryLoss : ∀ v,
      (∑ e ∈ crossing \ B, if G.Inc v e then G.weight e else 0) ≤ boundaryLoss)
    (hinternalLoss : ∀ v,
      (∑ e ∈ internal \ P, if G.Inc v e then G.weight e else 0) ≤ internalLoss) :
    ∃ color : G.E → Fin K,
      G.IsFeasibleOn (B ∪ P) color ∧
      (∀ e ∈ B, color e = boundary e) ∧
      ∀ v, (∑ e ∈ Finset.univ \ (B ∪ P), if G.Inc v e then G.weight e else 0) ≤
        boundaryLoss+internalLoss := by
  classical
  have hdisj : Disjoint B P := hparts.mono hB hP
  let color : G.E → Fin K := fun e => if e ∈ B then boundary e else inside e
  refine ⟨color,
    feasibleOn_merge_of_vertex_color_separation B P hdisj boundary inside
      hboundary hinside hseparate, (fun e he => by simp [color,he]), ?_⟩
  have hresidual : Finset.univ \ (B ∪ P) = (crossing \ B) ∪ (internal \ P) := by
    ext e
    have hp : e ∈ crossing ∨ e ∈ internal := by
      have he : e ∈ crossing ∪ internal := by rw [hpartition]; exact Finset.mem_univ _
      exact Finset.mem_union.mp he
    have hcross : e ∈ crossing → e ∉ P := fun he hf =>
      Finset.disjoint_left.mp hparts he (hP hf)
    have hint : e ∈ internal → e ∉ B := fun he hf =>
      Finset.disjoint_left.mp hparts (hB hf) he
    simp only [Finset.mem_sdiff, Finset.mem_univ, true_and, Finset.mem_union]
    tauto
  have hremdisj : Disjoint (crossing \ B) (internal \ P) :=
    hparts.mono Finset.sdiff_subset Finset.sdiff_subset
  intro v
  rw [hresidual,Finset.sum_union hremdisj]
  exact add_le_add (hboundaryLoss v) (hinternalLoss v)

end
end WeightedEdgeColoring.Subtwo
