import WeightedEdgeColoring.SubtwoOrdinaryFivePresentMiddleAllExternal

/-!
# The old left endpoint has no BC chord to the third middle vertex
-/

namespace WeightedEdgeColoring.WeightedMultigraph

universe u
variable (G : WeightedMultigraph.{u})

theorem FivePathState.no_left_bc_adj_middle_third
    {F : Finset G.E} {k : ℕ} {a b c : Fin k}
    (s : G.FivePathState F k a b)
    (hleft : FivePathState.HasExternalColorAt G s c s.left) :
    ¬(G.twoColorGraph (F.erase s.omitted) s.paint b c).Adj
      s.left (s.path.1.getVert 3) := by
  obtain ⟨g, hgF, hgX, hgC, hgExt⟩ := hleft
  have hXS : s.left ∈ s.path.1.support.toFinset := by
    simpa only [List.mem_toFinset] using s.path.1.start_mem_support
  obtain ⟨w,hgw,hwOut,hwNeX⟩ :=
    FivePathState.outside_neighbor_of_external_edge G s hXS hgF hgExt
  obtain ⟨g₀,hg₀F,hg₀X,hg₀Z1,hg₀B⟩ :=
    FivePathState.exists_first_b_edge G s
  have hZ3S : s.path.1.getVert 3 ∈ s.path.1.support.toFinset := by
    simpa only [List.mem_toFinset] using s.path.1.getVert_mem_support 3
  have hZ13 : s.path.1.getVert 1 ≠ s.path.1.getVert 3 := by
    intro h
    have hi := s.path.property.getVert_injOn
      (Set.mem_Iic.mpr (by have := s.path_len; omega : 1 ≤ s.path.1.length))
      (Set.mem_Iic.mpr (by have := s.path_len; omega : 3 ≤ s.path.1.length)) h
    omega
  intro hadj
  obtain ⟨r,hrF,hrX,hrZ3,hrColor⟩ :=
    G.exists_twoColorWitnessEdge (F.erase s.omitted) s.paint b c hadj
  rcases hrColor with hrB | hrC
  · have hrg : r = g₀ := by
      apply s.proper s.left
      · exact Finset.mem_coe.mpr (Finset.mem_filter.mpr ⟨hrF,hrX⟩)
      · exact Finset.mem_coe.mpr (Finset.mem_filter.mpr ⟨hg₀F,hg₀X⟩)
      · exact hrB.trans hg₀B.symm
    subst r
    have hZ3Z1 := (G.kempeOtherEndpoint_eq_of_incident
      hrX hrZ3 hadj.ne).symm.trans
      (G.kempeOtherEndpoint_eq_of_incident hg₀X hg₀Z1
        (FivePathState.internal_vertex_ne_endpoints G s
          (by omega : 0 < 1) (by omega : 1 < 4)).1.symm)
    exact hZ13 hZ3Z1.symm
  · have hrg : r = g := by
      apply s.proper s.left
      · exact Finset.mem_coe.mpr (Finset.mem_filter.mpr ⟨hrF,hrX⟩)
      · exact Finset.mem_coe.mpr (Finset.mem_filter.mpr ⟨hgF,hgX⟩)
      · exact hrC.trans hgC.symm
    subst r
    have hZ3w := (G.kempeOtherEndpoint_eq_of_incident
      hrX hrZ3 hadj.ne).symm.trans
      (G.kempeOtherEndpoint_eq_of_incident hgX hgw hwNeX.symm)
    exact hwOut (hZ3w ▸ hZ3S)

end WeightedEdgeColoring.WeightedMultigraph
