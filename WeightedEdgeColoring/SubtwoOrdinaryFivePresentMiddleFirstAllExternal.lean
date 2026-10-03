import WeightedEdgeColoring.SubtwoOrdinaryFivePresentMiddleFirstChordContradiction
import WeightedEdgeColoring.SubtwoOrdinaryFivePresentOppositeContradiction
import WeightedEdgeColoring.SubtwoOrdinaryFivePresentMiddleAllExternal

/-!
# The all-external middle-first return reduces by one edge shift
-/

namespace WeightedEdgeColoring.WeightedMultigraph

universe u
variable (G : WeightedMultigraph.{u})

theorem FivePathState.external_at_z1_of_other_four_external
    {F : Finset G.E} {k D : ℕ} {a b c : Fin k}
    (s : G.FivePathState F k a b)
    (hcritical : G.IsColorCriticalOn F k)
    (hdk : D + 1 < k) (hdegree : ∀ z, G.degreeOn F z ≤ D)
    (hthreshold : 7 * D < 6 * k + 2)
    (hnot : FivePathState.NotTwoInternalColor G s c)
    (hleft : FivePathState.HasExternalColorAt G s c s.left)
    (hright : FivePathState.HasExternalColorAt G s c s.right)
    (hZ2 : FivePathState.HasExternalColorAt G s c
      (s.path.1.getVert 2))
    (hZ3 : FivePathState.HasExternalColorAt G s c
      (s.path.1.getVert 3)) :
    FivePathState.HasExternalColorAt G s c
      (s.path.1.getVert 1) := by
  let S := s.path.1.support.toFinset
  have hother : ∀ w ∈ S,
      w ≠ s.path.1.getVert 1 → w ≠ s.path.1.getVert 3 →
      FivePathState.HasExternalColorAt G s c w := by
    intro w hwS hwNe1 hwNe3
    have hS := FivePathState.support_eq_five_vertices G s
    change w ∈ s.path.1.support.toFinset at hwS
    rw [hS] at hwS
    simp only [Finset.mem_insert, Finset.mem_singleton] at hwS
    rcases hwS with hX | hZ1 | hZ2eq | hZ3eq | hY
    · simpa [hX] using hleft
    · exact False.elim (hwNe1 hZ1)
    · simpa [hZ2eq] using hZ2
    · exact False.elim (hwNe3 hZ3eq)
    · simpa [hY] using hright
  have hpresent := FivePathState.present_at_every_vertex_of_not_two_internal
    G s hcritical hdk hdegree hthreshold hnot
  have hpresent1 : c ∉ G.missingColorsAt
      (F.erase s.omitted) s.paint (s.path.1.getVert 1) :=
    hpresent _ (s.path.1.getVert_mem_support 1)
  have hno13 : ¬∃ g, g ∈ F.erase s.omitted ∧
      G.Inc (s.path.1.getVert 1) g ∧
      G.Inc (s.path.1.getVert 3) g ∧ s.paint g = c := by
    intro h
    obtain ⟨g,hgF,hg1,hg3,hgc⟩ := h
    obtain ⟨r,hrF,hr3,hrc,hrExt⟩ := hZ3
    have hgr : g = r := s.proper (s.path.1.getVert 3)
      (Finset.mem_coe.mpr (Finset.mem_filter.mpr ⟨hgF,hg3⟩))
      (Finset.mem_coe.mpr (Finset.mem_filter.mpr ⟨hrF,hr3⟩))
      (hgc.trans hrc.symm)
    have hne13 : s.path.1.getVert 1 ≠
        s.path.1.getVert 3 := by
      intro h
      have hidx := s.path.property.getVert_injOn
        (Set.mem_Iic.mpr (by have := s.path_len; omega : 1 ≤ s.path.1.length))
        (Set.mem_Iic.mpr (by have := s.path_len; omega : 3 ≤ s.path.1.length)) h
      omega
    have hEnds := G.endpoint_eq_or_endpoint_eq_swap_of_inc
      hne13 hg1 hg3
    have h1S : s.path.1.getVert 1 ∈
        s.path.1.support.toFinset := by
      simpa only [List.mem_toFinset] using
        s.path.1.getVert_mem_support 1
    have h3S : s.path.1.getVert 3 ∈
        s.path.1.support.toFinset := by
      simpa only [List.mem_toFinset] using
        s.path.1.getVert_mem_support 3
    have hgInt : g ∈ G.internalEdges (F.erase s.omitted)
        s.path.1.support.toFinset := by
      simp only [internalEdges, Finset.mem_filter]
      rcases hEnds with ⟨hf,hs⟩ | ⟨hf,hs⟩
      · exact ⟨hgF,hf.symm ▸ h1S,hs.symm ▸ h3S⟩
      · exact ⟨hgF,hf.symm ▸ h3S,hs.symm ▸ h1S⟩
    exact hrExt (hgr ▸ hgInt)
  exact G.external_color_at_of_present_no_middle_edge
    s.proper hpresent1
    (fun w hwS hwNe1 hwNe3 ↦ hother w hwS hwNe1 hwNe3)
    hno13

end WeightedEdgeColoring.WeightedMultigraph
