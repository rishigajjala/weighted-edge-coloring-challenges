import WeightedEdgeColoring.SubtwoTinyBlockAmbientRestoration
import WeightedEdgeColoring.SubtwoDisjointBlockRestoration

/-! Simultaneously restore every selected block in one shared palette. -/

open scoped BigOperators
namespace WeightedEdgeColoring.WeightedMultigraph.GeneralTinyThresholdPacketization
noncomputable section
universe u
variable {G : WeightedEdgeColoring.WeightedMultigraph.{u}} {tau : ℝ}
  (P : G.GeneralTinyThresholdPacketization tau)

theorem exists_allBlocks_restoration_of_local
    {n K : ℕ} (hn : 0 < n) (hK : 0 < K)
    (hlocal : P.mixedObjectGraph.LocallyPacksInto n)
    (boundaryLabel : ∀ b : (P.mixedObjectGraph.subtwoFloorQuotient n).V,
      Fin K → Option
        (P.mixedObjectGraph.vertexRestriction
          (P.mixedObjectGraph.floorPacketization.groupedGraph.subtwoFiber
            (P.mixedObjectGraph.subtwoFloorBlock n) b)).V)
    (loss : ℝ) (hloss0 : 0 ≤ loss)
    (hpositive : ∀ b : (P.mixedObjectGraph.subtwoFloorQuotient n).V,
      (P.mixedObjectGraph.floorPacketization.groupedGraph.subtwoFinalRank
        (P.mixedObjectGraph.subtwoFloorCost n) b = 1 ∨
       P.mixedObjectGraph.floorPacketization.groupedGraph.subtwoFinalRank
        (P.mixedObjectGraph.subtwoFloorCost n) b = 2) →
      let H := P.mixedObjectGraph
      let T := H.floorPacketization.groupedGraph.subtwoFiber (H.subtwoFloorBlock n) b
      let R : Finset (H.vertexRestriction T).E :=
        Finset.univ.filter (fun e => e.val ∈ P.coreObjects)
      let J := (H.vertexRestriction T).edgeRestriction R
      ∃ A : Finset J.E, ∃ color : J.E → Fin K,
        J.IsFeasibleOn A color ∧
        (∀ e ∈ A, ∀ v, J.Inc v e → boundaryLabel b (color e) ≠ some v) ∧
        ∀ v : J.V,
          (∑ o ∈ P.smallInternalObjects T,
            if H.Inc v.val o.1 then H.weight o.1 else 0) +
          (∑ e ∈ Finset.univ \ A, if J.Inc v e then J.weight e else 0) ≤ loss) :
    let H := P.mixedObjectGraph
    ∃ A ⊆ P.internalObjects n, ∃ color : H.E → Fin K,
      H.IsFeasibleOn A color ∧
      (∀ e ∈ A, ∀ v, H.Inc v e →
        (boundaryLabel (H.subtwoFloorBlock n v) (color e)).map Subtype.val ≠ some v) ∧
      ∀ v, (∑ e ∈ P.internalObjects n \ A,
        if H.Inc v e then H.weight e else 0) ≤ loss := by
  dsimp only
  let H := P.mixedObjectGraph
  let B := (H.subtwoFloorQuotient n).V
  let block : H.V → B := H.subtwoFloorBlock n
  let owner : H.E → B := P.objectOwner n
  have hinc : ∀ e ∈ P.internalObjects n, ∀ v, H.Inc v e →
      owner e = block v := P.internalObjects_owner_inc n
  have hlocalAll : ∀ b : B,
      ∃ Q ⊆ (P.internalObjects n).filter (fun e => owner e = b),
      ∃ color : H.E → Fin K,
        H.IsFeasibleOn Q color ∧
        (∀ e ∈ Q, ∀ v, H.Inc v e →
          (boundaryLabel b (color e)).map Subtype.val ≠ some v) ∧
        ∀ v, block v = b →
          (∑ e ∈ ((P.internalObjects n).filter fun e => owner e = b) \ Q,
            if H.Inc v e then H.weight e else 0) ≤ loss := by
    intro b
    let r := H.floorPacketization.groupedGraph.subtwoFinalRank
      (H.subtwoFloorCost n) b
    have hrle : r ≤ 2 := by
      unfold r WeightedMultigraph.subtwoFinalRank
      split_ifs <;> omega
    by_cases hr0 : r = 0
    · have hempty := P.internalObjects_owner_filter_empty_of_rank_zero
        hn hlocal b hr0
      refine ⟨∅, by simp, (fun _ => ⟨0,hK⟩), ?_, ?_, ?_⟩
      · intro v c
        simp [WeightedMultigraph.colorLoadOn]
      · intro e he
        simp at he
      · intro v hv
        change (∑ e ∈ ((P.internalObjects n).filter
          (fun e => P.objectOwner n e = b)) \ ∅,
          if H.Inc v e then H.weight e else 0) ≤ loss
        rw [hempty]
        simp [hloss0]
    · have hr : r = 1 ∨ r = 2 := by omega
      have hp := hpositive b hr
      exact P.exists_ambient_block_restoration_of_local n b K hK
        (boundaryLabel b) loss hp
  exact WeightedEdgeColoring.Subtwo.exists_blockwise_physical_restoration (G := H)
    (P.internalObjects n) block owner hinc
    (fun b c => (boundaryLabel b c).map Subtype.val)
    (fun _ v => v) loss hlocalAll

end
end WeightedEdgeColoring.WeightedMultigraph.GeneralTinyThresholdPacketization
