import WeightedEdgeColoring.SubtwoOrdinaryFivePresentMiddleExternal

/-!
# The middle vertices belong to Y's (b,c) component
-/

namespace WeightedEdgeColoring.WeightedMultigraph

universe u
variable (G : WeightedMultigraph.{u})

/-- If `Z₂` were outside the `(b,c)` component through `Y`, switching
that component would make a critical `(a,c)` path contain all five old
vertices and an exterior neighbor of `Z₂`. -/
theorem FivePathState.middle_second_in_right_bc_component
    {F : Finset G.E} {k D : ℕ} {a b c : Fin k}
    (s : G.FivePathState F k a b)
    (hcritical : G.IsColorCriticalOn F k)
    (hdk : D + 1 < k) (hdegree : ∀ z, G.degreeOn F z ≤ D)
    (hthreshold : 7 * D < 6 * k + 2)
    (hleft : FivePathState.HasExternalColorAt G s c s.left)
    (hright : FivePathState.HasExternalColorAt G s c s.right)
    (hZ2ext : FivePathState.HasExternalColorAt G s c
      (s.path.1.getVert 2))
    (p : (G.twoColorGraph (F.erase s.omitted) s.paint b c).Path
      s.right s.left) :
    (G.twoColorGraph (F.erase s.omitted) s.paint b c).connectedComponentMk
        (s.path.1.getVert 2) =
      (G.twoColorGraph (F.erase s.omitted) s.paint b c).connectedComponentMk
        s.right := by
  classical
  let H := G.twoColorGraph (F.erase s.omitted) s.paint b c
  by_contra hZ2not
  let flip : H.ConnectedComponent → Prop :=
    fun C ↦ C = H.connectedComponentMk s.right
  letI : DecidablePred flip := Classical.decPred _
  let switched := G.kempeComponentSwitch
    (F.erase s.omitted) s.paint b c flip
  have hproper : G.IsProperOn (F.erase s.omitted) switched :=
    G.isProperOn_kempeComponentSwitch
      (F.erase s.omitted) s.paint s.proper b c flip
  have hcne := FivePathState.external_endpoint_color_ne_missing
    G s hleft hright
  obtain ⟨g₀, hg₀F, hg₀X, hg₀Z1, hg₀B⟩ :=
    FivePathState.exists_first_b_edge G s
  have hab : a ≠ b := by
    intro h
    exact (G.color_ne_of_mem_missingColorsAt
      (F.erase s.omitted) s.paint s.left a s.left_missing
      hg₀F hg₀X) (hg₀B.trans h.symm)
  have hac : a ≠ c := hcne.1.symm
  have haX : a ∈ G.missingColorsAt (F.erase s.omitted)
      switched s.left :=
    (G.mem_missingColorsAt_kempeComponentSwitch_of_fixedColor_iff
      (F := F.erase s.omitted) s.paint b c flip s.left a
      hab hac).mpr s.left_missing
  have hcY : c ∈ G.missingColorsAt (F.erase s.omitted)
      switched s.right :=
    (G.mem_missingColorsAt_kempeComponentSwitch_of_flip
      (F.erase s.omitted) s.paint b c flip s.right rfl).1.mpr
      s.right_missing
  have hXYcomp : H.connectedComponentMk s.left =
      H.connectedComponentMk s.right :=
    (SimpleGraph.ConnectedComponent.sound
      (show H.Reachable s.right s.left from ⟨p.1⟩)).symm
  have hg₀Sw : switched g₀ = c := by
    change G.kempeComponentSwitch (F.erase s.omitted)
      s.paint b c flip g₀ = c
    rw [G.kempeComponentSwitch_eq_localPerm
      (F.erase s.omitted) s.paint b c flip hg₀F hg₀X]
    simp [kempeLocalPerm, flip, H, hXYcomp, hg₀B]
  obtain ⟨g₁, g₂, g₃, hg₁F, hg₁Z1, hg₁Z2, hg₁A,
    _, _, _, _, hg₃F, hg₃Z3, hg₃Y, hg₃A⟩ :=
    FivePathState.exists_three_surviving_path_edges G s
  have hother : ∀ r, s.paint r ≠ b → s.paint r ≠ c →
      switched r = s.paint r := by
    intro r hrb hrc
    exact G.kempeComponentSwitch_eq_of_color_ne
      s.paint b c flip r hrb hrc
  have hg₁Sw : switched g₁ = a :=
    (hother g₁ (by simpa [hg₁A] using hab)
      (by simpa [hg₁A] using hac)).trans hg₁A
  have hg₃Sw : switched g₃ = a :=
    (hother g₃ (by simpa [hg₃A] using hab)
      (by simpa [hg₃A] using hac)).trans hg₃A
  have hZ2S : s.path.1.getVert 2 ∈ s.path.1.support.toFinset := by
    simpa only [List.mem_toFinset] using s.path.1.getVert_mem_support 2
  obtain ⟨r, hrF, hrZ2, hrC, hrExt⟩ := hZ2ext
  obtain ⟨w, hrw, hwOut, hwNeZ2⟩ :=
    FivePathState.outside_neighbor_of_external_edge
      G s hZ2S hrF hrExt
  have hZ2notFlip : ¬flip (H.connectedComponentMk
      (s.path.1.getVert 2)) := hZ2not
  have hrSw : switched r = c := by
    change G.kempeComponentSwitch (F.erase s.omitted)
      s.paint b c flip r = c
    rw [G.kempeComponentSwitch_eq_localPerm
      (F.erase s.omitted) s.paint b c flip hrF hrZ2]
    simp [kempeLocalPerm, flip, H, hZ2notFlip, hrC]
  let K := G.twoColorGraph (F.erase s.omitted) switched a c
  have hXZ1 : K.Adj s.left (s.path.1.getVert 1) :=
    G.twoColorGraph_adj_of_witness_inc
      (FivePathState.internal_vertex_ne_endpoints G s
        (by omega : 0 < 1) (by omega : 1 < 4)).1.symm
      hg₀F hg₀X hg₀Z1 (Or.inr hg₀Sw)
  have hZ12 : K.Adj (s.path.1.getVert 1)
      (s.path.1.getVert 2) :=
    G.twoColorGraph_adj_of_witness_inc
      (s.path.1.adj_getVert_succ
        (i := 1) (by have := s.path_len; omega)).ne
      hg₁F hg₁Z1 hg₁Z2 (Or.inl hg₁Sw)
  have hZ3Y : K.Adj (s.path.1.getVert 3) s.right :=
    G.twoColorGraph_adj_of_witness_inc
      (FivePathState.internal_vertex_ne_endpoints G s
        (by omega : 0 < 3) (by omega : 3 < 4)).2
      hg₃F hg₃Z3 hg₃Y (Or.inl hg₃Sw)
  have hZ2W : K.Adj (s.path.1.getVert 2) w :=
    G.twoColorGraph_adj_of_witness_inc
      (by intro h; exact hwOut (h ▸ hZ2S))
      hrF hrZ2 hrw (Or.inr hrSw)
  have hcompAC := G.critical_endpoints_same_twoColorComponent_at
    hcritical s.omitted_mem hproper s.left_ne_right
    s.left_inc s.right_inc haX hcY
  have hreachAC : K.Reachable s.left s.right :=
    SimpleGraph.ConnectedComponent.exact hcompAC
  obtain ⟨walk⟩ := hreachAC
  let qAC := walk.toPath
  have hXZ1comp := SimpleGraph.ConnectedComponent.connectedComponentMk_eq_of_adj hXZ1
  have hZ12comp := SimpleGraph.ConnectedComponent.connectedComponentMk_eq_of_adj hZ12
  have hZ3Ycomp := SimpleGraph.ConnectedComponent.connectedComponentMk_eq_of_adj hZ3Y
  have hZ2Wcomp := SimpleGraph.ConnectedComponent.connectedComponentMk_eq_of_adj hZ2W
  have hcompOld : ∀ v ∈ s.path.1.support,
      K.connectedComponentMk v = K.connectedComponentMk s.left := by
    intro v hv
    have hS := FivePathState.support_eq_five_vertices G s
    have hvS : v ∈ s.path.1.support.toFinset := by simpa using hv
    rw [hS] at hvS
    simp only [Finset.mem_insert, Finset.mem_singleton] at hvS
    rcases hvS with hX | hZ1 | hZ2 | hZ3 | hY
    · simpa [hX]
    · simpa [hZ1] using hXZ1comp.symm
    · simpa [hZ2] using hZ12comp.symm.trans hXZ1comp.symm
    · simpa only [hZ3] using hZ3Ycomp.trans hcompAC.symm
    · simpa [hY] using hcompAC.symm
  have hwComp : K.connectedComponentMk w =
      K.connectedComponentMk s.left :=
    hZ2Wcomp.symm.trans (hZ12comp.symm.trans hXZ1comp.symm)
  exact G.criticalPath_not_contains_fivePath_and_external_at
    s hcritical s.omitted_mem hproper s.left_ne_right
    s.left_inc s.right_inc haX hcY qAC
    hdk hdegree hthreshold hcompOld hwOut hwComp

/-- Without a middle `c` edge, both middle vertices lie on the
`(b,c)` component through `Y`. -/
theorem FivePathState.middle_pair_in_right_bc_component_of_no_middle_c
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
    (p : (G.twoColorGraph (F.erase s.omitted) s.paint b c).Path
      s.right s.left)
    (hnoMiddle : ¬∃ g, g ∈ F.erase s.omitted ∧
      G.Inc (s.path.1.getVert 2) g ∧
      G.Inc (s.path.1.getVert 3) g ∧ s.paint g = c) :
    (G.twoColorGraph (F.erase s.omitted) s.paint b c).connectedComponentMk
        (s.path.1.getVert 2) =
      (G.twoColorGraph (F.erase s.omitted) s.paint b c).connectedComponentMk
        s.right ∧
    (G.twoColorGraph (F.erase s.omitted) s.paint b c).connectedComponentMk
        (s.path.1.getVert 3) =
      (G.twoColorGraph (F.erase s.omitted) s.paint b c).connectedComponentMk
        s.right := by
  obtain ⟨hZ2ext, _⟩ :=
    FivePathState.external_middle_pair_of_no_middle_c
      G s hcritical hdk hdegree hthreshold hnot
      hleft hright hZ1 hnoMiddle
  have hZ2 := FivePathState.middle_second_in_right_bc_component
    G s hcritical hdk hdegree hthreshold
    hleft hright hZ2ext p
  obtain ⟨_, g2, _, _, _, _, _,
    hg2F, hg2Z2, hg2Z3, hg2B, _, _, _, _⟩ :=
    FivePathState.exists_three_surviving_path_edges G s
  have hAdj : (G.twoColorGraph (F.erase s.omitted) s.paint b c).Adj
      (s.path.1.getVert 2) (s.path.1.getVert 3) :=
    G.twoColorGraph_adj_of_witness_inc
      (s.path.1.adj_getVert_succ
        (i := 2) (by have := s.path_len; omega)).ne
      hg2F hg2Z2 hg2Z3 (Or.inl hg2B)
  have hComp :=
    SimpleGraph.ConnectedComponent.connectedComponentMk_eq_of_adj hAdj
  exact ⟨hZ2, hComp.symm.trans hZ2⟩

end WeightedEdgeColoring.WeightedMultigraph
