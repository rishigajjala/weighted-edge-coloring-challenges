import WeightedEdgeColoring.SubtwoBoundaryQuotientSupport

/-! The uncolored physical boundary is exactly the selected quotient residual's complement. -/

namespace WeightedEdgeColoring.WeightedMultigraph
open scoped BigOperators
noncomputable section
set_option maxHeartbeats 1500000
universe u
variable (G : WeightedMultigraph.{u})
variable {Q : Type u} [Fintype Q] [DecidableEq Q]

theorem physicalBoundary_leftover_eq_residual_image
    (block : G.V → Q) {K : ℕ}
    (C : (G.subtwoQuotient block).GeneralColoredPacketBase K)
    (F : Finset G.E) (hfull : C.fullEdges = G.subtwoQuotientSelectedEdges block F)
    (R : Finset C.residualGraph.E) :
    G.subtwoCrossingSelectedEdges block Finset.univ \
      (G.subtwoCrossingSelectedEdges block F ∪ G.selectedResidualOriginalEdges block C R) =
      (Finset.univ \ R).image (fun e : C.residualGraph.E => e.1.1) := by
  classical
  ext e
  constructor
  · intro he
    obtain ⟨hecross,heout⟩ := Finset.mem_sdiff.mp he
    have hcross := (Finset.mem_filter.mp hecross).2
    have hnotF : e ∉ F := by
      intro heF
      exact heout (Finset.mem_union_left _ (Finset.mem_filter.mpr ⟨heF,hcross⟩))
    let eQ : (G.subtwoQuotient block).E := ⟨e,hcross⟩
    have heR : eQ ∈ C.residualEdges := by
      apply Finset.mem_sdiff.mpr
      refine ⟨Finset.mem_univ _,?_⟩
      rw [hfull]
      intro heF
      exact hnotF (Finset.mem_filter.mp heF).2
    let eR : C.residualGraph.E := ⟨eQ,heR⟩
    apply Finset.mem_image.mpr
    refine ⟨eR, Finset.mem_sdiff.mpr ⟨Finset.mem_univ _,?_⟩,rfl⟩
    intro heRR
    apply heout
    exact Finset.mem_union_right _ (Finset.mem_image.mpr ⟨eR,heRR,rfl⟩)
  · intro he
    obtain ⟨eR,heR,rfl⟩ := Finset.mem_image.mp he
    apply Finset.mem_sdiff.mpr
    refine ⟨Finset.mem_filter.mpr ⟨Finset.mem_univ _,eR.1.2⟩,?_⟩
    intro hused
    rcases Finset.mem_union.mp hused with hbase | hres
    · apply (Finset.mem_sdiff.mp eR.2).2
      rw [hfull]
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,(Finset.mem_filter.mp hbase).1⟩
    · obtain ⟨f,hf,heq⟩ := Finset.mem_image.mp hres
      have hfeq : f = eR := Subtype.ext (Subtype.ext heq)
      exact (Finset.mem_sdiff.mp heR).2 (hfeq ▸ hf)

theorem physicalBoundary_leftover_weight_le_quotient
    (block : G.V → Q) {K : ℕ}
    (C : (G.subtwoQuotient block).GeneralColoredPacketBase K)
    (F : Finset G.E) (hfull : C.fullEdges = G.subtwoQuotientSelectedEdges block F)
    (R : Finset C.residualGraph.E) (v : G.V) :
    (∑ e ∈ G.subtwoCrossingSelectedEdges block Finset.univ \
      (G.subtwoCrossingSelectedEdges block F ∪ G.selectedResidualOriginalEdges block C R),
      if G.Inc v e then G.weight e else 0) ≤
    ∑ e ∈ Finset.univ \ R,
      if C.residualGraph.Inc (block v) e then C.residualGraph.weight e else 0 := by
  classical
  rw [G.physicalBoundary_leftover_eq_residual_image block C F hfull R]
  rw [Finset.sum_image (by
    intro e _ f _ hef
    exact Subtype.ext (Subtype.ext hef))]
  apply Finset.sum_le_sum
  intro e _
  by_cases hi : G.Inc v e.1.1
  · have hq : C.residualGraph.Inc (block v) e := by
      rcases hi with h | h
      · exact Or.inl (congrArg block h)
      · exact Or.inr (congrArg block h)
    simp only [hi,hq,if_true]
    exact le_rfl
  · simp only [hi,if_false]
    split_ifs
    · exact C.residualGraph.weight_nonneg e
    · exact le_rfl

theorem physicalBoundary_base_disjoint_residual
    (block : G.V → Q) {K : ℕ}
    (C : (G.subtwoQuotient block).GeneralColoredPacketBase K)
    (F : Finset G.E) (hfull : C.fullEdges = G.subtwoQuotientSelectedEdges block F)
    (R : Finset C.residualGraph.E) :
    Disjoint (G.subtwoCrossingSelectedEdges block F)
      (G.selectedResidualOriginalEdges block C R) := by
  classical
  rw [Finset.disjoint_left]
  intro e he hf
  obtain ⟨f,_,rfl⟩ := Finset.mem_image.mp hf
  apply (Finset.mem_sdiff.mp f.2).2
  rw [hfull]
  exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,(Finset.mem_filter.mp he).1⟩

end
end WeightedEdgeColoring.WeightedMultigraph
