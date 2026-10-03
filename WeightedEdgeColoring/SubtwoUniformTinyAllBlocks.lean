import WeightedEdgeColoring.SubtwoTinyAllBlockAssembly

/-! One grouping width and threshold before the graph, then one shared
palette for every selected dense block in that graph. -/

open scoped BigOperators
namespace WeightedEdgeColoring.WeightedMultigraph
noncomputable section
universe u

theorem exists_uniform_tinyAllBlocks_physical_restoration
    (Sbound : ℕ) (hSbound : 0 < Sbound) (η : ℝ) (hη : 0 < η) :
    ∃ M N : ℕ, 0 < M ∧ 0 < N ∧
      ∀ (G : WeightedMultigraph.{u})
        (P : G.GeneralTinyThresholdPacketization ((1:ℝ)/Sbound))
        (n : ℕ), N ≤ n →
      P.mixedObjectGraph.LocallyPacksInto n →
      ∀ (D K : ℕ), 0 < K →
      ∀ (boundaryLabel :
        ∀ b : (P.mixedObjectGraph.subtwoFloorQuotient n).V,
          Fin K → Option
            (P.mixedObjectGraph.vertexRestriction
              (P.mixedObjectGraph.floorPacketization.groupedGraph.subtwoFiber
                (P.mixedObjectGraph.subtwoFloorBlock n) b)).V),
      (∀ b v,
        (Fintype.card {c : Fin K // boundaryLabel b c = some v} : ℝ) ≤
          n * (P.mixedObjectGraph.subtwoExteriorHarmonicCharge
            (P.mixedObjectGraph.floorPacketization.groupedGraph.subtwoFiber
              (P.mixedObjectGraph.subtwoFloorBlock n) b) v.val / n) + D) →
      (n : ℝ)*(1999/1000:ℝ)+5*(D+1) ≤ K →
      let H := P.mixedObjectGraph
      ∃ A ⊆ P.internalObjects n, ∃ color : H.E → Fin K,
        H.IsFeasibleOn A color ∧
        (∀ e ∈ A, ∀ v, H.Inc v e →
          (boundaryLabel (H.subtwoFloorBlock n v) (color e)).map Subtype.val ≠ some v) ∧
        ∀ v, (∑ e ∈ P.internalObjects n \ A,
          if H.Inc v e then H.weight e else 0) ≤
            25 / (Sbound : ℝ) + η*n := by
  obtain ⟨M,N,hM,hN,hrest⟩ :=
    exists_uniform_tinyBlock_physical_restoration
      Sbound hSbound η hη
  refine ⟨M,N,hM,hN,?_⟩
  intro G P n hnN hlocal D K hK boundaryLabel hlabels hpalette
  have hn : 0 < n := lt_of_lt_of_le hN hnN
  have hloss0 : (0:ℝ) ≤ 25/(Sbound:ℝ)+η*n := by positivity
  apply P.exists_allBlocks_restoration_of_local hn hK hlocal
    boundaryLabel (25/(Sbound:ℝ)+η*n) hloss0
  intro b hrank
  exact hrest G P n hnN hlocal b hrank D K hK
    (boundaryLabel b) (hlabels b) hpalette

end
end WeightedEdgeColoring.WeightedMultigraph
