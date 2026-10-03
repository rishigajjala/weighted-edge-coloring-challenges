import WeightedEdgeColoring.SubtwoUniformTinyAllBlocks
import WeightedEdgeColoring.SubtwoWholePartialAssembly

/-! Complete a supported boundary coloring using the uniform internal-block theorem. -/

namespace WeightedEdgeColoring.WeightedMultigraph
open scoped BigOperators
noncomputable section
universe u

theorem exists_uniform_tinyBoundary_completion
    (S : ℕ) (hS : 0 < S) (η : ℝ) (hη : 0 < η) :
    ∃ N : ℕ, 0 < N ∧
      ∀ (G : WeightedMultigraph.{u})
        (P : G.GeneralTinyThresholdPacketization ((1 : ℝ) / S))
        (n : ℕ), N ≤ n → P.mixedObjectGraph.LocallyPacksInto n →
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
      (n : ℝ) * (1999 / 1000 : ℝ) + 5 * (D + 1) ≤ K →
      ∀ (B : Finset P.Object) (boundary : P.Object → Fin K) (loss : ℝ),
      B ⊆ P.mixedObjectGraph.subtwoCrossingSelectedEdges
        (P.mixedObjectGraph.subtwoFloorBlock n) Finset.univ →
      P.mixedObjectGraph.IsFeasibleOn B boundary →
      (∀ e ∈ B, ∀ v, P.mixedObjectGraph.Inc v e →
        (boundaryLabel (P.mixedObjectGraph.subtwoFloorBlock n v)
          (boundary e)).map Subtype.val = some v) →
      (∀ v, (∑ e ∈ P.mixedObjectGraph.subtwoCrossingSelectedEdges
          (P.mixedObjectGraph.subtwoFloorBlock n) Finset.univ \ B,
        if P.mixedObjectGraph.Inc v e then P.mixedObjectGraph.weight e else 0) ≤ loss) →
      ∃ (F : Finset P.Object) (color : P.Object → Fin K),
        P.mixedObjectGraph.IsFeasibleOn F color ∧
        (∀ e ∈ B, color e = boundary e) ∧
        ∀ v, (∑ e ∈ Finset.univ \ F,
          if P.mixedObjectGraph.Inc v e then P.mixedObjectGraph.weight e else 0) ≤
            loss + 25 / (S : ℝ) + η * n := by
  classical
  obtain ⟨M,N,hM,hN,hrest⟩ :=
    exists_uniform_tinyAllBlocks_physical_restoration S hS η hη
  refine ⟨N,hN,?_⟩
  intro G P n hn hlocal D K hK labels hlabels hpalette B boundary loss
    hB hboundary hsupport hloss
  obtain ⟨A,hA,inside,hinside,havoid,hinternalLoss⟩ :=
    hrest G P n hn hlocal D K hK labels hlabels hpalette
  let H := P.mixedObjectGraph
  let crossing := H.subtwoCrossingSelectedEdges (H.subtwoFloorBlock n) Finset.univ
  have hpartition : crossing ∪ P.internalObjects n = Finset.univ := by
    ext e
    simp only [crossing, H, subtwoCrossingSelectedEdges,
      GeneralTinyThresholdPacketization.internalObjects, Finset.mem_union,
      Finset.mem_filter, Finset.mem_univ, true_and, iff_true]
    tauto
  have hparts : Disjoint crossing (P.internalObjects n) := by
    rw [Finset.disjoint_left]
    intro e he hf
    exact (Finset.mem_filter.mp he).2 (Finset.mem_filter.mp hf).2
  have hseparate : ∀ e ∈ B, ∀ f ∈ A, ∀ v,
      H.Inc v e → H.Inc v f → boundary e ≠ inside f := by
    intro e he f hf v hev hfv heq
    apply havoid f hf v hfv
    rw [← heq]
    exact hsupport e he v hev
  obtain ⟨color,hfeas,hkeep,hrem⟩ :=
    Subtwo.exists_whole_partialColor_of_boundary_and_internal
      crossing (P.internalObjects n) B A hpartition hparts hB hA
      boundary inside hboundary hinside hseparate
      loss (25 / (S : ℝ) + η * n) hloss hinternalLoss
  refine ⟨B ∪ A,color,hfeas,hkeep,?_⟩
  intro v
  simpa only [add_assoc] using hrem v

end
end WeightedEdgeColoring.WeightedMultigraph
