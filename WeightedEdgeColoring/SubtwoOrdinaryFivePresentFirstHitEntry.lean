import WeightedEdgeColoring.SubtwoOrdinaryFivePresentFirstHit

/-!
# The color of an ordered first-return edge
-/

namespace WeightedEdgeColoring.WeightedMultigraph

universe u
variable (G : WeightedMultigraph.{u})

/-- At a first return to an internal five-path vertex, the entering
edge is an external `c` edge when that vertex already has its internal
`b` edge. This supplies the boundary-color witness used in Andersen's
remaining first-return cases. -/
theorem FivePathState.external_color_at_first_return_of_internal_b_edge
    {F : Finset G.E} {k : ℕ} {a b c : Fin k}
    (s : G.FivePathState F k a b)
    (p : (G.twoColorGraph (F.erase s.omitted) s.paint b c).Path
      s.right s.left)
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

theorem FivePathState.exists_first_b_edge
    {F : Finset G.E} {k : ℕ} {a b : Fin k}
    (s : G.FivePathState F k a b) :
    ∃ g, g ∈ F.erase s.omitted ∧
      G.Inc s.left g ∧ G.Inc (s.path.1.getVert 1) g ∧
      s.paint g = b := by
  have hadj : (G.twoColorGraph (F.erase s.omitted) s.paint a b).Adj
      s.left (s.path.1.getVert 1) := by
    simpa using s.path.1.adj_getVert_succ
      (i := 0) (by have := s.path_len; omega)
  obtain ⟨g, hgF, hgL, hg1, hgColor⟩ :=
    G.exists_twoColorWitnessEdge (F.erase s.omitted) s.paint a b hadj
  have hgNeA : s.paint g ≠ a :=
    G.color_ne_of_mem_missingColorsAt
      (F.erase s.omitted) s.paint s.left a s.left_missing hgF hgL
  exact ⟨g, hgF, hgL, hg1, hgColor.resolve_left hgNeA⟩

/-- The actual ordered first-return vertex carries an external `c`
edge. This is the local input for the remaining `V = Z₁` symmetry
branch in Andersen's argument. -/
theorem FivePathState.same_component_first_return_external
    {F : Finset G.E} {k d : ℕ} {a b c : Fin k}
    (s : G.FivePathState F k a b)
    (hcritical : G.IsColorCriticalOn F k)
    (hdk : d + 1 < k) (hdegree : ∀ z, G.degreeOn F z ≤ d)
    (hthreshold : 7 * d < 6 * k + 2)
    (hleft : FivePathState.HasExternalColorAt G s c s.left)
    (hright : FivePathState.HasExternalColorAt G s c s.right)
    (hcomp : (G.twoColorGraph (F.erase s.omitted) s.paint b c).connectedComponentMk
        s.right =
      (G.twoColorGraph (F.erase s.omitted) s.paint b c).connectedComponentMk
        s.left) :
    ∃ p : (G.twoColorGraph (F.erase s.omitted) s.paint b c).Path
      s.right s.left,
      ∃ i : ℕ, 1 < i ∧ i ≤ p.1.length ∧
        (∀ j, 0 < j → j < i →
          p.1.getVert j ∉ s.path.1.support.toFinset) ∧
        FivePathState.HasExternalColorAt G s c (p.1.getVert i) ∧
        (p.1.getVert i = s.path.1.getVert 1 ∨
          p.1.getVert i = s.path.1.getVert 2 ∨
          p.1.getVert i = s.path.1.getVert 3) := by
  obtain ⟨p, i, hi, hiLe, hfirst, hcase⟩ :=
    FivePathState.same_component_first_return_internal G s
      hcritical hdk hdegree hthreshold hleft hright hcomp
  obtain ⟨g₀, hg₀F, hg₀L, hg₀1, hg₀B⟩ :=
    FivePathState.exists_first_b_edge G s
  obtain ⟨g₁, g₂, g₃, _, _, _, _,
    hg₂F, hg₂2, hg₂3, hg₂B, _, _, _, _⟩ :=
    FivePathState.exists_three_surviving_path_edges G s
  have hLmem : s.left ∈ s.path.1.support.toFinset := by
    simpa only [List.mem_toFinset] using s.path.1.start_mem_support
  have hZ2mem : s.path.1.getVert 2 ∈ s.path.1.support.toFinset := by
    simpa only [List.mem_toFinset] using s.path.1.getVert_mem_support 2
  have hZ3mem : s.path.1.getVert 3 ∈ s.path.1.support.toFinset := by
    simpa only [List.mem_toFinset] using s.path.1.getVert_mem_support 3
  have hZ23ne : s.path.1.getVert 2 ≠ s.path.1.getVert 3 :=
    (s.path.1.adj_getVert_succ
      (i := 2) (by have := s.path_len; omega)).ne
  have hExt : FivePathState.HasExternalColorAt G s c (p.1.getVert i) := by
    rcases hcase with hZ1 | hZ2 | hZ3
    · have hzne :=
        (FivePathState.internal_vertex_ne_endpoints G s
          (by omega : 0 < 1) (by omega : 1 < 4)).1
      exact FivePathState.external_color_at_first_return_of_internal_b_edge
        G s p hi hiLe hfirst hg₀F (hZ1 ▸ hg₀1) hg₀L
        (hZ1 ▸ hzne) hLmem hg₀B
    · exact FivePathState.external_color_at_first_return_of_internal_b_edge
        G s p hi hiLe hfirst hg₂F (hZ2 ▸ hg₂2) hg₂3
        (hZ2 ▸ hZ23ne) hZ3mem hg₂B
    · exact FivePathState.external_color_at_first_return_of_internal_b_edge
        G s p hi hiLe hfirst hg₂F (hZ3 ▸ hg₂3) hg₂2
        (hZ3 ▸ hZ23ne.symm) hZ2mem hg₂B
  exact ⟨p, i, hi, hiLe, hfirst, hExt, hcase⟩

end WeightedEdgeColoring.WeightedMultigraph
