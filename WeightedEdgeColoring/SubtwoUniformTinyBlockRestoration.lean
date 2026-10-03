import WeightedEdgeColoring.SubtwoTinyBlockPhysicalRestoration

/-! The grouping parameters are chosen before the graph, its tiny
packetization, and the selected dense block. -/

open scoped BigOperators
namespace WeightedEdgeColoring.WeightedMultigraph
noncomputable section
universe u

theorem exists_uniform_tinyBlock_physical_restoration
    (Sbound : ℕ) (hSbound : 0 < Sbound) (η : ℝ) (hη : 0 < η) :
    ∃ M N : ℕ, 0 < M ∧ 0 < N ∧
      ∀ (G : WeightedMultigraph.{u})
        (P : G.GeneralTinyThresholdPacketization ((1:ℝ)/Sbound))
        (n : ℕ), N ≤ n →
      P.mixedObjectGraph.LocallyPacksInto n →
      ∀ (b : (P.mixedObjectGraph.subtwoFloorQuotient n).V),
      (P.mixedObjectGraph.floorPacketization.groupedGraph.subtwoFinalRank
        (P.mixedObjectGraph.subtwoFloorCost n) b = 1 ∨
       P.mixedObjectGraph.floorPacketization.groupedGraph.subtwoFinalRank
        (P.mixedObjectGraph.subtwoFloorCost n) b = 2) →
      ∀ (D K : ℕ), 0 < K →
      ∀ (boundaryLabel : Fin K → Option
        (P.mixedObjectGraph.vertexRestriction
          (P.mixedObjectGraph.floorPacketization.groupedGraph.subtwoFiber
            (P.mixedObjectGraph.subtwoFloorBlock n) b)).V),
      (∀ v,
        (Fintype.card {c : Fin K // boundaryLabel c = some v} : ℝ) ≤
          n * (P.mixedObjectGraph.subtwoExteriorHarmonicCharge
            (P.mixedObjectGraph.floorPacketization.groupedGraph.subtwoFiber
              (P.mixedObjectGraph.subtwoFloorBlock n) b) v.val / n) + D) →
      (n : ℝ)*(1999/1000:ℝ)+5*(D+1) ≤ K →
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
          (∑ e ∈ Finset.univ \ A, if J.Inc v e then J.weight e else 0) ≤
            25 / (Sbound : ℝ) + η*n := by
  obtain ⟨M,N,hM,hN,hparam⟩ :=
    SubtwoLinearGrouping.exists_uniform_smallBlockGroupingParameters
      Sbound η hη
  refine ⟨M,N,hM,hN,?_⟩
  intro G P n hnN hlocal b hrank D K hK boundaryLabel hlabel hpalette
  have hn : 0 < n := lt_of_lt_of_le hN hnN
  let H := P.mixedObjectGraph
  let T := H.floorPacketization.groupedGraph.subtwoFiber (H.subtwoFloorBlock n) b
  let R : Finset (H.vertexRestriction T).E :=
    Finset.univ.filter (fun e => e.val ∈ P.coreObjects)
  let J := (H.vertexRestriction T).edgeRestriction R
  have hT : T.card ≤ 5 := P.selectedBlock_card_le_five hn hlocal b hrank
  have hV : Fintype.card J.V ≤ 5 := by
    change Fintype.card (H.vertexRestriction T).V ≤ 5
    rw [H.vertexRestriction_card]
    exact hT
  have hlocalJ : J.LocallyPacksInto n :=
    (H.vertexRestriction T).edgeRestriction_locallyPacksInto R
      (H.vertexRestriction_locallyPacksInto T hlocal)
  have hlower : ∀ e : J.E, (1:ℝ)/Sbound ≤ J.weight e := by
    intro e
    exact P.retainedBlock_weight_ge T R
      (by intro x hx; exact (Finset.mem_filter.mp hx).2) e
  have hcard := J.subtwo_card_edges_le_of_weight_floor Sbound hSbound hlower hlocalJ
  have herr := hparam J n hnN hV hcard
  obtain ⟨A,color,hfeas,havoid,hraw⟩ :=
    P.exists_retainedBlock_physical_restoration hSbound hn hlocal b
      hrank M D K hM hK boundaryLabel hlabel hpalette
  refine ⟨A,color,hfeas,havoid,?_⟩
  intro v
  have hv := hraw v
  linarith

end
end WeightedEdgeColoring.WeightedMultigraph
