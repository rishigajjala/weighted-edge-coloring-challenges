import WeightedEdgeColoring.SubtwoOrdinaryFivePresentVZ1InternalCContradiction

/-!
# External c edges at the two middle vertices when Z2–Z3 has no c edge
-/

namespace WeightedEdgeColoring.WeightedMultigraph

universe u
variable (G : WeightedMultigraph.{u})

/-- If a color is present at `v`, every other vertex of a set except
`z` already uses that color on an external edge, and no color edge
joins `v` to `z`, then its edge at `v` is external as well. -/
theorem external_color_at_of_present_no_middle_edge
    {F : Finset G.E} {k : ℕ} {paint : G.E → Fin k}
    (hproper : G.IsProperOn F paint)
    {S : Finset G.V} {v z : G.V} {c : Fin k}
    (hpresent : c ∉ G.missingColorsAt F paint v)
    (hother : ∀ w ∈ S, w ≠ v → w ≠ z →
      ∃ r, r ∈ F ∧ G.Inc w r ∧ paint r = c ∧
        r ∉ G.internalEdges F S)
    (hnoMiddle : ¬∃ g, g ∈ F ∧ G.Inc v g ∧ G.Inc z g ∧
      paint g = c) :
    ∃ g, g ∈ F ∧ G.Inc v g ∧ paint g = c ∧
      g ∉ G.internalEdges F S := by
  obtain ⟨g, hgF, hgv, hgc⟩ :=
    G.exists_edge_of_not_missingColor hpresent
  refine ⟨g, hgF, hgv, hgc, ?_⟩
  intro hgInternal
  have hgData := Finset.mem_filter.mp hgInternal
  have huData : ∃ w, G.Inc w g ∧ w ≠ v ∧ w ∈ S := by
    rcases hgv with hvF | hvS
    · refine ⟨G.snd g, Or.inr rfl, ?_, hgData.2.2⟩
      intro h
      exact G.noLoop g (hvF.trans h.symm)
    · refine ⟨G.fst g, Or.inl rfl, ?_, hgData.2.1⟩
      intro h
      exact G.noLoop g (h.trans hvS.symm)
  obtain ⟨w, hgw, hwNeV, hwS⟩ := huData
  have hwNeZ : w ≠ z := by
    intro h
    exact hnoMiddle ⟨g, hgF, hgv, h ▸ hgw, hgc⟩
  obtain ⟨r, hrF, hrW, hrc, hrExt⟩ :=
    hother w hwS hwNeV hwNeZ
  have hgr : g = r := hproper w
    (Finset.mem_coe.mpr (Finset.mem_filter.mpr ⟨hgF, hgw⟩))
    (Finset.mem_coe.mpr (Finset.mem_filter.mpr ⟨hrF, hrW⟩))
    (hgc.trans hrc.symm)
  exact hrExt (hgr ▸ hgInternal)

/-- In the present-color branch, if `c` has no middle `Z₂–Z₃`
edge, it must leave the old five vertices at both `Z₂` and `Z₃`. -/
theorem FivePathState.external_middle_pair_of_no_middle_c
    {F : Finset G.E} {k D : ℕ} {a b c : Fin k}
    (s : G.FivePathState F k a b)
    (hcritical : G.IsColorCriticalOn F k)
    (hdk : D + 1 < k) (hdegree : ∀ z, G.degreeOn F z ≤ D)
    (hthreshold : 7 * D < 6 * k + 2)
    (hnot : FivePathState.NotTwoInternalColor G s c)
    (hleft : FivePathState.HasExternalColorAt G s c s.left)
    (hright : FivePathState.HasExternalColorAt G s c s.right)
    (hZ1 : FivePathState.HasExternalColorAt G s c
      (s.path.1.getVert 1))
    (hnoMiddle : ¬∃ g, g ∈ F.erase s.omitted ∧
      G.Inc (s.path.1.getVert 2) g ∧
      G.Inc (s.path.1.getVert 3) g ∧ s.paint g = c) :
    FivePathState.HasExternalColorAt G s c (s.path.1.getVert 2) ∧
      FivePathState.HasExternalColorAt G s c
        (s.path.1.getVert 3) := by
  let S := s.path.1.support.toFinset
  have hother : ∀ w ∈ S,
      w ≠ s.path.1.getVert 2 → w ≠ s.path.1.getVert 3 →
      FivePathState.HasExternalColorAt G s c w := by
    intro w hwS hwNe2 hwNe3
    have hS := FivePathState.support_eq_five_vertices G s
    change w ∈ s.path.1.support.toFinset at hwS
    rw [hS] at hwS
    simp only [Finset.mem_insert, Finset.mem_singleton] at hwS
    rcases hwS with hX | hZ1eq | hZ2 | hZ3 | hY
    · simpa [hX] using hleft
    · simpa [hZ1eq] using hZ1
    · exact False.elim (hwNe2 hZ2)
    · exact False.elim (hwNe3 hZ3)
    · simpa [hY] using hright
  have hpresent := FivePathState.present_at_every_vertex_of_not_two_internal
    G s hcritical hdk hdegree hthreshold hnot
  have hpresent2 : c ∉ G.missingColorsAt
      (F.erase s.omitted) s.paint (s.path.1.getVert 2) :=
    hpresent _ (s.path.1.getVert_mem_support 2)
  have hpresent3 : c ∉ G.missingColorsAt
      (F.erase s.omitted) s.paint (s.path.1.getVert 3) :=
    hpresent _ (s.path.1.getVert_mem_support 3)
  have hExt2 : FivePathState.HasExternalColorAt G s c
      (s.path.1.getVert 2) := by
    exact G.external_color_at_of_present_no_middle_edge
      s.proper hpresent2
      (fun w hwS hwNe2 hwNe3 ↦ hother w hwS hwNe2 hwNe3)
      hnoMiddle
  have hnoMiddleRev : ¬∃ g, g ∈ F.erase s.omitted ∧
      G.Inc (s.path.1.getVert 3) g ∧
      G.Inc (s.path.1.getVert 2) g ∧ s.paint g = c := by
    intro h
    obtain ⟨g, hgF, hg3, hg2, hgc⟩ := h
    exact hnoMiddle ⟨g, hgF, hg2, hg3, hgc⟩
  have hExt3 : FivePathState.HasExternalColorAt G s c
      (s.path.1.getVert 3) := by
    exact G.external_color_at_of_present_no_middle_edge
      s.proper hpresent3
      (fun w hwS hwNe3 hwNe2 ↦ hother w hwS hwNe2 hwNe3)
      hnoMiddleRev
  exact ⟨hExt2, hExt3⟩

end WeightedEdgeColoring.WeightedMultigraph
