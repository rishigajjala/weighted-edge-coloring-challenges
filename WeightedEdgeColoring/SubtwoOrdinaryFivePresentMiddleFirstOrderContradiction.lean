import WeightedEdgeColoring.SubtwoOrdinaryFivePresentMiddleBDCycle

/-!
# Contradiction when Z₂ precedes Z₃ on the Y-rooted BC chain
-/

namespace WeightedEdgeColoring.WeightedMultigraph

universe u
variable (G : WeightedMultigraph.{u})

theorem FivePathState.false_of_vz1_no_middle_c_z2_first
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
      G.Inc (s.path.1.getVert 3) g ∧ s.paint g = c)
    (p : (G.twoColorGraph (F.erase s.omitted) s.paint b c).Path
      s.right s.left)
    {i : ℕ} (hi : 1 < i) (hiLe : i ≤ p.1.length)
    (hfirst : ∀ j, 0 < j → j < i →
      p.1.getVert j ∉ s.path.1.support.toFinset)
    (hiZ1 : p.1.getVert i = s.path.1.getVert 1)
    (q₃ : (G.twoColorGraph (F.erase s.omitted) s.paint b c).Path
      s.right (s.path.1.getVert 3))
    (hqLen : p.1.length ≤ q₃.1.length)
    (hX : q₃.1.getVert p.1.length = s.left)
    (hpen : q₃.1.getVert (q₃.1.length-1) =
      s.path.1.getVert 2) : False := by
  obtain ⟨u,huL,huR,hu1,hu2,hu3,hZ2Ext,hZ3Ext,hYExt,
    paint₂,hproper,hcLeft,haRight,hother,hstable,hfixed,qCA,hqCard⟩ :=
    FivePathState.exists_actual_middle_second_switch
      G s hcritical hdk hdegree hthreshold hnot
        hleft hright hZ1 hnoMiddle p hi hiLe hfirst hiZ1
        q₃ hqLen hX hpen
  obtain ⟨outY,outZ,hne,hYoutS,hZoutS,gY,gZ,gA,
    hgYF,hgZF,hgAF,hgYY,hgYOut,hgYC,
    hgZZ2,hgZOut,hgZC,hgAY,hgAZ,hgAA⟩ :=
    FivePathState.forced_middle_outside_a_edge
      G s u hcritical huL huR hu1 hu2 hu3
        hZ2Ext hZ3Ext hYExt
        hproper hcLeft haRight hother hstable qCA hqCard
  have hSupport : u.path.1.support.toFinset =
      s.path.1.support.toFinset := by
    rw [FivePathState.support_eq_five_vertices G u,
      FivePathState.support_eq_five_vertices G s]
    simp only [huL,huR,hu1,hu2,hu3]
    ext v
    simp only [Finset.mem_insert,Finset.mem_singleton]
    tauto
  have hYout : outY ∉ u.path.1.support.toFinset := by
    simpa [hSupport] using hYoutS
  have hZout : outZ ∉ u.path.1.support.toFinset := by
    simpa [hSupport] using hZoutS
  have hleftExtU : FivePathState.HasExternalColorAt G u c u.left := by
    simpa [huL] using hZ3Ext
  have hrightExtU : FivePathState.HasExternalColorAt G u c u.right := by
    simpa [huR] using hYExt
  obtain ⟨d,hda,hdb,hdc,hdLeft,hdLeft₂,hqLenCA,hqSupport,
    gD₁,gD₂,hgD₁F,hgD₂F,hgD₁Y,hgD₁1,
    hgD₂2,hgD₂3,hgD₁D,hgD₂D,hgD₁₂,hgD₂₂⟩ :=
    FivePathState.middle_d_edge_locations_of_forced_geometry
      G u hcritical hdk hdegree hthreshold
        hleftExtU hrightExtU
        hproper hcLeft haRight hother hfixed qCA hqCard
        hne hYout hZout
        hgYF (huR ▸ hgYY) hgYOut hgYC
        hgZF (hu1 ▸ hgZZ2) hgZOut hgZC
  obtain ⟨g₁,_,g₃,hg₁F,hg₁1,hg₁2,hg₁B,
    _,_,_,_,hg₃F,hg₃3,hg₃Y,hg₃B⟩ :=
    FivePathState.exists_three_surviving_path_edges G u
  have hZ2S : s.path.1.getVert 2 ∈ s.path.1.support :=
    s.path.1.getVert_mem_support 2
  have hXS : s.left ∈ s.path.1.support := s.path.1.start_mem_support
  have hZ2neZ3 : s.path.1.getVert 2 ≠ s.path.1.getVert 3 :=
    (s.path.1.adj_getVert_succ
      (i := 2) (by have := s.path_len; omega)).ne
  have hXneZ3 : s.left ≠ s.path.1.getVert 3 :=
    (FivePathState.internal_vertex_ne_endpoints G s
      (by omega : 0 < 3) (by omega : 3 < 4)).1.symm
  have hg₁₂ : paint₂ g₁ = b :=
    (hstable (s.path.1.getVert 2) hZ2S hZ2neZ3
      g₁ hg₁F (hu1 ▸ hg₁1)).trans hg₁B
  have hg₃₂ : paint₂ g₃ = b :=
    (hstable s.left hXS hXneZ3
      g₃ hg₃F (hu3 ▸ hg₃3)).trans hg₃B
  obtain ⟨qBD,hqBDLen,hclose,hLeftOut,_,_,_⟩ :=
    FivePathState.exists_middle_bd_cycle_of_four_edges
      G u hgD₁F hgD₁Y hgD₁1 hgD₁₂
        hg₁F hg₁1 hg₁2 hg₁₂
        hgD₂F hgD₂2 hgD₂3 hgD₂₂
        hg₃F hg₃3 hg₃Y hg₃₂
  have hPath3out : u.path.1.getVert 3 ∉ qCA.1.support.toFinset := by
    intro hm
    rw [hqSupport] at hm
    simp only [Finset.mem_insert,Finset.mem_singleton] at hm
    rcases hm with hL | h1 | hZ | hY | hR
    · have hne := (FivePathState.internal_vertex_ne_endpoints G u
        (by omega : 0 < 3) (by omega : 3 < 4)).1
      exact hne hL
    · have hinj := u.path.property.getVert_injOn
        (Set.mem_Iic.mpr (by have := u.path_len; omega : 3 ≤ u.path.1.length))
        (Set.mem_Iic.mpr (by have := u.path_len; omega : 1 ≤ u.path.1.length)) h1
      omega
    · exact hZout (hZ ▸ (by simpa only [List.mem_toFinset] using
        u.path.1.getVert_mem_support 3))
    · exact hYout (hY ▸ (by simpa only [List.mem_toFinset] using
        u.path.1.getVert_mem_support 3))
    · exact (FivePathState.internal_vertex_ne_endpoints G u
        (by omega : 0 < 3) (by omega : 3 < 4)).2 hR
  have hab : a ≠ b := by
    obtain ⟨g₀,hg₀F,hg₀L,_,hg₀A⟩ :=
      FivePathState.exists_first_b_edge G u
    intro heq
    exact (G.color_ne_of_mem_missingColorsAt
      (F.erase u.omitted) u.paint u.left b u.left_missing
      hg₀F hg₀L) (hg₀A.trans heq)
  have hcne := FivePathState.external_endpoint_color_ne_missing
    G u hleftExtU hrightExtU
  exact FivePathState.false_of_middle_bd_circuit_outside_ca_path
    G u hcritical hdk hdegree hthreshold
      hab hda.symm hcne.1 hdc.symm
      hproper hcLeft haRight hdLeft₂
      qCA hqLenCA hPath3out qBD hqBDLen hclose hLeftOut
      hg₃F hg₃3 hg₃Y hg₃₂

end WeightedEdgeColoring.WeightedMultigraph
