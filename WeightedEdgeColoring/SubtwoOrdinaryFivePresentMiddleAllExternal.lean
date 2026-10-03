import WeightedEdgeColoring.SubtwoOrdinaryFivePresentMiddleRotateTransport

/-!
# A color carried externally at every five-path vertex has no internal edge
-/

namespace WeightedEdgeColoring.WeightedMultigraph

universe u
variable (G : WeightedMultigraph.{u})

theorem FivePathState.no_internal_color_of_external_all
    {F : Finset G.E} {k : ℕ} {a b c : Fin k}
    (s : G.FivePathState F k a b)
    (hExt : ∀ v ∈ s.path.1.support.toFinset,
      FivePathState.HasExternalColorAt G s c v) :
    ∀ g ∈ G.internalEdges (F.erase s.omitted)
      s.path.1.support.toFinset, s.paint g ≠ c := by
  intro g hgInt hgC
  have hgData := Finset.mem_filter.mp hgInt
  have hgF := hgData.1
  have hgv : G.Inc (G.fst g) g := Or.inl rfl
  obtain ⟨r,hrF,hrV,hrC,hrExt⟩ :=
    hExt (G.fst g) hgData.2.1
  have hgr : g = r := s.proper (G.fst g)
    (Finset.mem_coe.mpr (Finset.mem_filter.mpr ⟨hgF,hgv⟩))
    (Finset.mem_coe.mpr (Finset.mem_filter.mpr ⟨hrF,hrV⟩))
    (hgC.trans hrC.symm)
  exact hrExt (hgr ▸ hgInt)

theorem FivePathState.not_two_internal_of_external_all
    {F : Finset G.E} {k : ℕ} {a b c : Fin k}
    (s : G.FivePathState F k a b)
    (hExt : ∀ v ∈ s.path.1.support.toFinset,
      FivePathState.HasExternalColorAt G s c v) :
    FivePathState.NotTwoInternalColor G s c := by
  intro htwo
  obtain ⟨g,_,_,hg,_,hgC,_⟩ := htwo
  exact (FivePathState.no_internal_color_of_external_all G s hExt g hg) hgC

end WeightedEdgeColoring.WeightedMultigraph
