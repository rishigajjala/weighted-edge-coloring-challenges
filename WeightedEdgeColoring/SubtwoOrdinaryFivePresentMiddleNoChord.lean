import WeightedEdgeColoring.SubtwoOrdinaryFivePresentExteriorTwoSwitch

/-!
# The old left endpoint has no BC chord to the second middle vertex
-/

namespace WeightedEdgeColoring.WeightedMultigraph

universe u
variable (G : WeightedMultigraph.{u})

theorem FivePathState.no_left_bc_adj_middle_second
    {F : Finset G.E} {k : ℕ} {a b c : Fin k}
    (s : G.FivePathState F k a b)
    (hleft : FivePathState.HasExternalColorAt G s c s.left) :
    ¬(G.twoColorGraph (F.erase s.omitted) s.paint b c).Adj
      s.left (s.path.1.getVert 2) := by
  obtain ⟨g, hgF, hgX, hgC, hgExt⟩ := hleft
  have hXS : s.left ∈ s.path.1.support.toFinset := by
    simpa only [List.mem_toFinset] using s.path.1.start_mem_support
  obtain ⟨w,hgw,hwOut,hwNeX⟩ :=
    FivePathState.outside_neighbor_of_external_edge G s hXS hgF hgExt
  obtain ⟨g₀,hg₀F,hg₀X,hg₀Z1,hg₀B⟩ :=
    FivePathState.exists_first_b_edge G s
  have hZ2S : s.path.1.getVert 2 ∈ s.path.1.support.toFinset := by
    simpa only [List.mem_toFinset] using s.path.1.getVert_mem_support 2
  have hZ12 : s.path.1.getVert 1 ≠ s.path.1.getVert 2 :=
    (s.path.1.adj_getVert_succ
      (i := 1) (by have := s.path_len; omega)).ne
  intro hadj
  obtain ⟨r,hrF,hrX,hrZ2,hrColor⟩ :=
    G.exists_twoColorWitnessEdge (F.erase s.omitted) s.paint b c hadj
  rcases hrColor with hrB | hrC
  · have hrg : r = g₀ := by
      apply s.proper s.left
      · exact Finset.mem_coe.mpr (Finset.mem_filter.mpr ⟨hrF,hrX⟩)
      · exact Finset.mem_coe.mpr (Finset.mem_filter.mpr ⟨hg₀F,hg₀X⟩)
      · exact hrB.trans hg₀B.symm
    subst r
    have hZ2Z1 := (G.kempeOtherEndpoint_eq_of_incident
      hrX hrZ2 hadj.ne).symm.trans
      (G.kempeOtherEndpoint_eq_of_incident hg₀X hg₀Z1
        (FivePathState.internal_vertex_ne_endpoints G s
          (by omega : 0 < 1) (by omega : 1 < 4)).1.symm)
    exact hZ12 hZ2Z1.symm
  · have hrg : r = g := by
      apply s.proper s.left
      · exact Finset.mem_coe.mpr (Finset.mem_filter.mpr ⟨hrF,hrX⟩)
      · exact Finset.mem_coe.mpr (Finset.mem_filter.mpr ⟨hgF,hgX⟩)
      · exact hrC.trans hgC.symm
    subst r
    have hZ2w := (G.kempeOtherEndpoint_eq_of_incident
      hrX hrZ2 hadj.ne).symm.trans
      (G.kempeOtherEndpoint_eq_of_incident hgX hgw hwNeX.symm)
    exact hwOut (hZ2w ▸ hZ2S)

end WeightedEdgeColoring.WeightedMultigraph
