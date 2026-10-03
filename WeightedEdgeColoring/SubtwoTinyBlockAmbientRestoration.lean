import WeightedEdgeColoring.SubtwoTinyBlockEdgePartition

/-! A local retained-block restoration becomes an ambient mixed-object
partial coloring with exactly the same endpoint labels and loss. -/

open scoped BigOperators
namespace WeightedEdgeColoring.WeightedMultigraph.GeneralTinyThresholdPacketization
noncomputable section
universe u
variable {G : WeightedEdgeColoring.WeightedMultigraph.{u}} {tau : ℝ}
  (P : G.GeneralTinyThresholdPacketization tau)

theorem exists_ambient_block_restoration_of_local
    (n : ℕ) (b : (P.mixedObjectGraph.subtwoFloorQuotient n).V)
    (K : ℕ) (hK : 0 < K)
    (boundaryLabel : Fin K → Option
      (P.mixedObjectGraph.vertexRestriction
        (P.mixedObjectGraph.floorPacketization.groupedGraph.subtwoFiber
          (P.mixedObjectGraph.subtwoFloorBlock n) b)).V)
    (loss : ℝ)
    (hlocal :
      let H := P.mixedObjectGraph
      let T := H.floorPacketization.groupedGraph.subtwoFiber (H.subtwoFloorBlock n) b
      let R : Finset (H.vertexRestriction T).E :=
        Finset.univ.filter (fun e => e.val ∈ P.coreObjects)
      let J := (H.vertexRestriction T).edgeRestriction R
      ∃ A : Finset J.E, ∃ color : J.E → Fin K,
        J.IsFeasibleOn A color ∧
        (∀ e ∈ A, ∀ v, J.Inc v e → boundaryLabel (color e) ≠ some v) ∧
        ∀ v : J.V,
          (∑ o ∈ P.smallInternalObjects T,
            if H.Inc v.val o.1 then H.weight o.1 else 0) +
          (∑ e ∈ Finset.univ \ A, if J.Inc v e then J.weight e else 0) ≤ loss) :
    let H := P.mixedObjectGraph
    ∃ A ⊆ (P.internalObjects n).filter (fun o => P.objectOwner n o = b),
      ∃ color : H.E → Fin K,
        H.IsFeasibleOn A color ∧
        (∀ e ∈ A, ∀ v, H.Inc v e →
          (boundaryLabel (color e)).map Subtype.val ≠ some v) ∧
        ∀ v, H.subtwoFloorBlock n v = b →
          (∑ e ∈ ((P.internalObjects n).filter (fun o => P.objectOwner n o = b)) \ A,
            if H.Inc v e then H.weight e else 0) ≤ loss := by
  dsimp only at hlocal ⊢
  let H := P.mixedObjectGraph
  let T := H.floorPacketization.groupedGraph.subtwoFiber (H.subtwoFloorBlock n) b
  let R : Finset (H.vertexRestriction T).E :=
    Finset.univ.filter (fun e => e.val ∈ P.coreObjects)
  let J := (H.vertexRestriction T).edgeRestriction R
  let edge : J.E → H.E := fun e => e.val.val
  obtain ⟨A,color,hfeas,havoid,hleft⟩ := hlocal
  obtain ⟨ambient,hambient,hsame,hambientAvoid,hambientLeft⟩ :=
    P.exists_ambient_lift_of_retainedBlock_color T R A K hK color hfeas
      boundaryLabel havoid
  have hsub : A.image edge ⊆
      (P.internalObjects n).filter (fun o => P.objectOwner n o = b) := by
    intro o ho
    have hpart := P.internalObjects_owner_filter_partition n b
    dsimp only at hpart
    have hcore : o ∈ (Finset.univ : Finset J.E).image edge :=
      Finset.image_subset_image (Finset.subset_univ A) ho
    exact hpart.symm ▸ (Finset.mem_union.mpr (Or.inr hcore))
  refine ⟨A.image edge,hsub,ambient,hambient,hambientAvoid,?_⟩
  intro v hv
  have hvt : v ∈ T := by
    exact (H.mem_subtwoFiber (H.subtwoFloorBlock n) b v).mpr hv
  let w : J.V := ⟨v,hvt⟩
  have hsplit := P.internalObjects_owner_leftover_split n b A v
  have hrem := hambientLeft w
  have hbound := hleft w
  dsimp only at hsplit
  rw [hsplit, hrem]
  exact hbound

end
end WeightedEdgeColoring.WeightedMultigraph.GeneralTinyThresholdPacketization
