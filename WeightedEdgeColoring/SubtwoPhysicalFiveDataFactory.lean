import WeightedEdgeColoring.SubtwoPhysicalFiveVector

/-! Construct the five-index physical data for every actual rank-two block. -/

set_option autoImplicit false

namespace WeightedEdgeColoring.WeightedMultigraph
noncomputable section
universe u
variable (G : WeightedMultigraph.{u})

theorem exists_subtwoFivePhysicalData_of_rank_two_block
    {n : ℕ} (hn : 0 < n) (hlocal : G.LocallyPacksInto n)
    (q : (G.subtwoFloorQuotient n).V)
    (hrank : G.floorPacketization.groupedGraph.subtwoFinalRank (G.subtwoFloorCost n) q = 2)
    (price : G.E → ℝ) (hp : ∀ e, 0 ≤ price e)
    (hR : 0 < G.subtwoColorPriceMax price) :
    ∃ D : G.SubtwoFivePhysicalData n,
      D.vertexSet = G.floorPacketization.groupedGraph.subtwoFiber (G.subtwoFloorBlock n) q ∧
      D.price = price := by
  classical
  let S := G.floorPacketization.groupedGraph.subtwoFiber (G.subtwoFloorBlock n) q
  have hcard := G.floorPacketization.groupedGraph.subtwoFinalBlock_fiber_card
    (G.subtwoFloorCost n) (G.subtwoFloorCost_nonneg n)
    (G.subtwoFloorCost_pair_le hn hlocal) (G.subtwoFloorCost_degree_le hn hlocal) q
  change S.card = 1 + 2 * G.floorPacketization.groupedGraph.subtwoFinalRank (G.subtwoFloorCost n) q at hcard
  rw [hrank] at hcard
  norm_num at hcard
  let φ : Fin 5 ≃ S := (Finset.equivFinOfCardEq hcard).symm
  let vertex : Fin 5 → G.V := fun i => (φ i).val
  have hinj : Function.Injective vertex := Subtype.val_injective.comp φ.injective
  let D := G.subtwoFivePhysicalDataOfLocalPacking hn hlocal vertex hinj price hp hR
  refine ⟨D, ?_, rfl⟩
  change Finset.univ.image vertex = S
  ext v
  constructor
  · intro hv
    obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hv
    exact (φ i).property
  · intro hv
    let i := φ.symm ⟨v, hv⟩
    refine Finset.mem_image.mpr ⟨i, Finset.mem_univ _, ?_⟩
    exact congrArg Subtype.val (φ.apply_symm_apply ⟨v, hv⟩)

end
end WeightedEdgeColoring.WeightedMultigraph
