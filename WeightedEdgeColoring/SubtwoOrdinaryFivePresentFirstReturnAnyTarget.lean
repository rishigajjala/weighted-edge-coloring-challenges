import WeightedEdgeColoring.SubtwoOrdinaryFivePresentAllFirstReturns

namespace WeightedEdgeColoring.WeightedMultigraph

universe u
variable (G : WeightedMultigraph.{u})

theorem FivePathState.external_color_at_first_return_of_internal_b_edge_any_target
    {F : Finset G.E} {k : ℕ} {a b c : Fin k}
    (s : G.FivePathState F k a b)
    {target : G.V}
    (p : (G.twoColorGraph (F.erase s.omitted) s.paint b c).Path
      s.right target)
    {i : ℕ} (hi : 1 < i) (hiLe : i ≤ p.1.length)
    (hfirst : ∀ j, 0 < j → j < i →
      p.1.getVert j ∉ s.path.1.support.toFinset)
    {g : G.E} (hgF : g ∈ F.erase s.omitted)
    (hgV : G.Inc (p.1.getVert i) g)
    {z : G.V} (hgz : G.Inc z g)
    (hzne : p.1.getVert i ≠ z)
    (hzS : z ∈ s.path.1.support.toFinset)
    (hgB : s.paint g = b) :
    FivePathState.HasExternalColorAt G s c (p.1.getVert i) := by
  have hprevPos : 0 < i - 1 := by omega
  have hprevLt : i - 1 < i := by omega
  have hprevOut := hfirst (i - 1) hprevPos hprevLt
  have hidx : i - 1 + 1 = i := by omega
  have hadj : (G.twoColorGraph (F.erase s.omitted) s.paint b c).Adj
      (p.1.getVert (i - 1)) (p.1.getVert i) := by
    simpa [hidx] using p.1.adj_getVert_succ (i := i - 1) (by omega)
  obtain ⟨r, hrF, hrPrev, hrV, hrColor⟩ :=
    G.exists_twoColorWitnessEdge (F.erase s.omitted) s.paint b c hadj
  have hrne : r ≠ g := by
    intro h
    have hrOther := G.kempeOtherEndpoint_eq_of_incident
      hrV hrPrev hadj.ne.symm
    have hgOther := G.kempeOtherEndpoint_eq_of_incident
      hgV hgz hzne
    rw [h] at hrOther
    have hprevZ : p.1.getVert (i - 1) = z :=
      hrOther.symm.trans hgOther
    exact hprevOut (hprevZ ▸ hzS)
  have hrNeB : s.paint r ≠ b := by
    intro h
    have heq := s.proper (p.1.getVert i)
      (Finset.mem_coe.mpr (Finset.mem_filter.mpr ⟨hrF, hrV⟩))
      (Finset.mem_coe.mpr (Finset.mem_filter.mpr ⟨hgF, hgV⟩))
      (h.trans hgB.symm)
    exact hrne heq
  have hrC : s.paint r = c := hrColor.resolve_left hrNeB
  have hrExt : r ∉ G.internalEdges (F.erase s.omitted)
      s.path.1.support.toFinset := by
    intro hInternal
    have hdata := Finset.mem_filter.mp hInternal
    rcases hrPrev with h | h
    · exact hprevOut (h ▸ hdata.2.1)
    · exact hprevOut (h ▸ hdata.2.2)
  exact ⟨r, hrF, hrV, hrC, hrExt⟩

end WeightedEdgeColoring.WeightedMultigraph
