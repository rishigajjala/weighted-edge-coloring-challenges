import WeightedEdgeColoring.SubtwoPhysicalBoundaryLoss
import WeightedEdgeColoring.SubtwoPhysicalPaletteMerge

/-! Merge the actual full packets and supported residual colors on the physical boundary. -/

namespace WeightedEdgeColoring.WeightedMultigraph
open scoped BigOperators
noncomputable section
set_option maxHeartbeats 2000000
universe u
variable (G : WeightedMultigraph.{u})
variable {Q : Type u} [Fintype Q] [DecidableEq Q]

theorem physicalBoundary_subset_crossing
    (block : G.V → Q) {K : ℕ}
    (C : (G.subtwoQuotient block).GeneralColoredPacketBase K)
    (F : Finset G.E) (R : Finset C.residualGraph.E) :
    G.subtwoCrossingSelectedEdges block F ∪ G.selectedResidualOriginalEdges block C R ⊆
      G.subtwoCrossingSelectedEdges block Finset.univ := by
  intro e he
  rcases Finset.mem_union.mp he with hb | hr
  · exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, (Finset.mem_filter.mp hb).2⟩
  · obtain ⟨f,_,rfl⟩ := Finset.mem_image.mp hr
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,f.1.2⟩

theorem exists_physicalBoundary_partialColor
    (block : G.V → Q)
    (hfiber : ∀ q, (G.subtwoFiber block q).card ≤ 5)
    {K : ℕ} (hK : 0 < K)
    (C : (G.subtwoQuotient block).GeneralColoredPacketBase K)
    (F : Finset G.E)
    (hfull : C.fullEdges = G.subtwoQuotientSelectedEdges block F)
    (hunique : ∀ e ∈ G.subtwoCrossingSelectedEdges block F,
      ∀ f ∈ G.subtwoCrossingSelectedEdges block F,
      ∀ v w, G.Inc v e → G.Inc w f → block v = block w →
        G.subtwoLiftQuotientColor hK block C.baseColor e =
          G.subtwoLiftQuotientColor hK block C.baseColor f → v = w)
    (R : Finset C.residualGraph.E) (color : C.residualGraph.E → Fin K)
    (hfeasible : C.residualGraph.IsFeasibleOn R color)
    (hmissing : ∀ e ∈ R,
      color e ∈ (G.subtwoQuotient block).missingColorsAt
          C.fullEdges C.baseColor ((G.subtwoQuotient block).fst e.1) ∧
      color e ∈ (G.subtwoQuotient block).missingColorsAt
          C.fullEdges C.baseColor ((G.subtwoQuotient block).snd e.1))
    (selectedLabel : Q → Fin K → Option (Fin 6))
    (hselected : ∀ e ∈ R, ∀ q (hinc : C.residualGraph.Inc q e),
      selectedLabel q (color e) =
        some (G.subtwoQuotientResidualEdgeLabel block hfiber C q ⟨e,hinc⟩))
    (loss : ℝ)
    (hloss : ∀ q, (∑ e ∈ Finset.univ \ R,
      if C.residualGraph.Inc q e then C.residualGraph.weight e else 0) ≤ loss) :
    let boundaryEdges := G.subtwoCrossingSelectedEdges block F ∪
      G.selectedResidualOriginalEdges block C R
    ∃ (boundary : G.E → Fin K) (labels : Q → Fin K → Option (Fin 6)),
      G.IsFeasibleOn boundaryEdges boundary ∧
      (∀ e ∈ boundaryEdges, ∀ v, G.Inc v e →
        labels (block v) (boundary e) =
          some (G.subtwoLocalSixLabel block hfiber (block v) v)) ∧
      (∀ q label,
        (Finset.univ.filter fun c : Fin K => labels q c = some label).card ≤
          (Finset.univ.filter fun c : Fin K =>
            ∃ v, block v = q ∧
              (∃ e ∈ G.subtwoCrossingSelectedEdges block F,
                G.Inc v e ∧ G.subtwoLiftQuotientColor hK block C.baseColor e = c) ∧
              G.subtwoLocalSixLabel block hfiber q v = label).card +
          (Finset.univ.filter fun c : Fin K => selectedLabel q c = some label).card) ∧
      ∀ v, (∑ e ∈ G.subtwoCrossingSelectedEdges block Finset.univ \ boundaryEdges,
        if G.Inc v e then G.weight e else 0) ≤ loss := by
  classical
  dsimp only
  let proposal : C.residualGraph.E → Fin K → ℝ := fun e c =>
    if e ∈ R ∧ c = color e then 1 else 0
  have hpositive : ∀ e ∈ R, 0 < proposal e (color e) := by
    intro e he
    simp [proposal,he]
  have hsupport : ∀ e c, 0 < proposal e c →
      c ∈ (G.subtwoQuotient block).missingColorsAt
          C.fullEdges C.baseColor ((G.subtwoQuotient block).fst e.1) ∧
      c ∈ (G.subtwoQuotient block).missingColorsAt
          C.fullEdges C.baseColor ((G.subtwoQuotient block).snd e.1) := by
    intro e c hc
    have hcond : e ∈ R ∧ c = color e := by
      by_contra h
      simp [proposal,h] at hc
    rw [hcond.2]
    exact hmissing e hcond.1
  let Fb := G.subtwoCrossingSelectedEdges block F
  let Fr := G.selectedResidualOriginalEdges block C R
  let base := G.subtwoLiftQuotientColor hK block C.baseColor
  let residual := G.liftSelectedResidualOriginalColor block hK C color
  have hdisj : Disjoint Fb Fr := G.physicalBoundary_base_disjoint_residual block C F hfull R
  have hbase : G.IsFeasibleOn Fb base :=
    G.feasibleOn_liftQuotientPacketBase block hK C F hfull
  have hresidual : G.IsFeasibleOn Fr residual :=
    G.feasibleOn_liftSelectedResidualOriginalColor block hK C R color hfeasible
  have hseparate : ∀ e ∈ Fb, ∀ f ∈ Fr, ∀ v,
      G.Inc v e → G.Inc v f → base e ≠ residual f := by
    intro e he f hf v hev hfv heq
    have hnot := G.liftedResidual_not_boundaryBaseUses
      block hK C F hfull R color proposal hsupport hpositive hf hfv
    exact hnot ⟨v,rfl,e,he,hev,heq⟩
  obtain ⟨labels,hbaseLabels,hresLabels,hcounts⟩ :=
    G.exists_combinedPhysicalBoundaryLabel block hfiber hK C F hfull
      hunique R color proposal hsupport hpositive selectedLabel hselected
  let boundary : G.E → Fin K := fun e => if e ∈ Fb then base e else residual e
  refine ⟨boundary,labels,?_,?_,hcounts,?_⟩
  · exact Subtwo.feasibleOn_merge_of_vertex_color_separation
      Fb Fr hdisj base residual hbase hresidual hseparate
  · intro e he v hev
    rcases Finset.mem_union.mp he with hb | hr
    · change e ∈ Fb at hb
      simp only [boundary,if_pos hb]
      exact hbaseLabels e hb v hev
    · have hb : e ∉ Fb := fun he => Finset.disjoint_left.mp hdisj he hr
      simp only [boundary,if_neg hb]
      exact hresLabels e hr v hev
  · intro v
    exact (G.physicalBoundary_leftover_weight_le_quotient block C F hfull R v).trans
      (hloss (block v))

end
end WeightedEdgeColoring.WeightedMultigraph
