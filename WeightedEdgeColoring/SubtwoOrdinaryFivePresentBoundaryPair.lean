import WeightedEdgeColoring.SubtwoOrdinaryFivePresentFirstHitEntry

/-!
# Distinct exterior neighbors at two vertices of the five-path
-/

namespace WeightedEdgeColoring.WeightedMultigraph

universe u
variable (G : WeightedMultigraph.{u})

/-- Two distinct vertices of the five-path whose `c` edges leave the
five-path reach distinct exterior vertices in a proper coloring. -/
theorem FivePathState.distinct_outside_neighbors_of_external_pair
    {F : Finset G.E} {k : ℕ} {a b c : Fin k}
    (s : G.FivePathState F k a b)
    {v z : G.V} (hvS : v ∈ s.path.1.support.toFinset)
    (hzS : z ∈ s.path.1.support.toFinset) (hvz : v ≠ z)
    (hv : FivePathState.HasExternalColorAt G s c v)
    (hz : FivePathState.HasExternalColorAt G s c z) :
    ∃ u w, u ≠ w ∧
      u ∉ s.path.1.support.toFinset ∧
      w ∉ s.path.1.support.toFinset ∧
      ∃ g r, g ∈ F.erase s.omitted ∧ r ∈ F.erase s.omitted ∧
        G.Inc v g ∧ G.Inc u g ∧
        G.Inc z r ∧ G.Inc w r ∧
        s.paint g = c ∧ s.paint r = c := by
  obtain ⟨g, hgF, hgv, hgc, hgExt⟩ := hv
  obtain ⟨r, hrF, hrz, hrc, hrExt⟩ := hz
  obtain ⟨u, hgu, huOut, huNeV⟩ :=
    FivePathState.outside_neighbor_of_external_edge G s hvS hgF hgExt
  obtain ⟨w, hrw, hwOut, hwNeZ⟩ :=
    FivePathState.outside_neighbor_of_external_edge G s hzS hrF hrExt
  have hgr : g ≠ r := by
    intro h
    have huNeZ : u ≠ z := by
      intro huz
      exact huOut (huz ▸ hzS)
    have hVother := G.kempeOtherEndpoint_eq_of_incident
      hgu hgv huNeV
    have hZother := G.kempeOtherEndpoint_eq_of_incident
      (h ▸ hgu) hrz huNeZ
    exact hvz ((h ▸ hVother).symm.trans hZother)
  have huw : u ≠ w := by
    intro h
    have heq : g = r := s.proper u
      (Finset.mem_coe.mpr (Finset.mem_filter.mpr ⟨hgF, hgu⟩))
      (Finset.mem_coe.mpr (Finset.mem_filter.mpr ⟨hrF, h ▸ hrw⟩))
      (hgc.trans hrc.symm)
    exact hgr heq
  exact ⟨u, w, huw, huOut, hwOut,
    g, r, hgF, hrF, hgv, hgu, hrz, hrw, hgc, hrc⟩

end WeightedEdgeColoring.WeightedMultigraph
