import WeightedEdgeColoring.SubtwoOrdinaryFivePresentMiddleSecondSwitchActual

/-!
# The short critical CA path forces an exterior a edge
-/

namespace WeightedEdgeColoring.WeightedMultigraph

universe u
variable (G : WeightedMultigraph.{u})

theorem FivePathState.forced_middle_outside_a_edge
    {F : Finset G.E} {k : ℕ} {a b c : Fin k}
    (s : G.FivePathState F k a b)
    (u : G.FivePathState F k b a)
    (hcritical : G.IsColorCriticalOn F k)
    (huL : u.left = s.path.1.getVert 3)
    (huR : u.right = s.right)
    (hu1 : u.path.1.getVert 1 = s.path.1.getVert 2)
    (hu2 : u.path.1.getVert 2 = s.path.1.getVert 1)
    (hu3 : u.path.1.getVert 3 = s.left)
    (hZ2Ext : FivePathState.HasExternalColorAt G u c
      (s.path.1.getVert 2))
    (hZ3Ext : FivePathState.HasExternalColorAt G u c
      (s.path.1.getVert 3))
    (hYExt : FivePathState.HasExternalColorAt G u c s.right)
    {paint₂ : G.E → Fin k}
    (hproper₂ : G.IsProperOn (F.erase u.omitted) paint₂)
    (hcLeft : c ∈ G.missingColorsAt (F.erase u.omitted) paint₂ u.left)
    (haRight : a ∈ G.missingColorsAt (F.erase u.omitted) paint₂ u.right)
    (hother : ∀ r, u.paint r ≠ b → u.paint r ≠ c →
      paint₂ r = u.paint r)
    (hstable : ∀ v ∈ s.path.1.support,
      v ≠ s.path.1.getVert 3 →
        ∀ r ∈ F.erase u.omitted, G.Inc v r →
          paint₂ r = u.paint r)
    (qCA : (G.twoColorGraph (F.erase u.omitted) paint₂ c a).Path
      u.left u.right)
    (hqCard : qCA.1.support.toFinset.card ≤ 5) :
    ∃ outY outZ : G.V,
      outY ≠ outZ ∧
      outY ∉ s.path.1.support.toFinset ∧
      outZ ∉ s.path.1.support.toFinset ∧
      ∃ gY gZ gA : G.E,
        gY ∈ F.erase u.omitted ∧
        gZ ∈ F.erase u.omitted ∧
        gA ∈ F.erase u.omitted ∧
        G.Inc s.right gY ∧ G.Inc outY gY ∧ paint₂ gY = c ∧
        G.Inc (s.path.1.getVert 2) gZ ∧ G.Inc outZ gZ ∧
          paint₂ gZ = c ∧
        G.Inc outY gA ∧ G.Inc outZ gA ∧ paint₂ gA = a := by
  have hSupport : u.path.1.support.toFinset =
      s.path.1.support.toFinset := by
    rw [FivePathState.support_eq_five_vertices G u,
      FivePathState.support_eq_five_vertices G s]
    simp only [huL,huR,hu1,hu2,hu3]
    ext v
    simp only [Finset.mem_insert,Finset.mem_singleton]
    tauto
  have hZ2U : s.path.1.getVert 2 ∈ u.path.1.support.toFinset := by
    simpa only [List.mem_toFinset,←hu1] using
      u.path.1.getVert_mem_support 1
  have hYU : s.right ∈ u.path.1.support.toFinset := by
    simpa only [List.mem_toFinset,←huR] using u.path.1.end_mem_support
  have hYZ2 : s.right ≠ s.path.1.getVert 2 :=
    (FivePathState.internal_vertex_ne_endpoints G s
      (by omega : 0 < 2) (by omega : 2 < 4)).2.symm
  obtain ⟨outY,outZ,hne,hYoutU,hZoutU,gY,gZ,
    hgYF,hgZF,hgYY,hgYOut,hgZZ2,hgZOut,hgYC,hgZC⟩ :=
    FivePathState.distinct_outside_neighbors_of_external_pair
      G u hYU hZ2U hYZ2 hYExt hZ2Ext
  have hYout : outY ∉ s.path.1.support.toFinset := by
    simpa [hSupport] using hYoutU
  have hZout : outZ ∉ s.path.1.support.toFinset := by
    simpa [hSupport] using hZoutU
  have hYmem : s.right ∈ s.path.1.support := s.path.1.end_mem_support
  have hZ2mem : s.path.1.getVert 2 ∈ s.path.1.support :=
    s.path.1.getVert_mem_support 2
  have hYneZ3 : s.right ≠ s.path.1.getVert 3 :=
    (FivePathState.internal_vertex_ne_endpoints G s
      (by omega : 0 < 3) (by omega : 3 < 4)).2.symm
  have hZ2neZ3 : s.path.1.getVert 2 ≠ s.path.1.getVert 3 :=
    (s.path.1.adj_getVert_succ
      (i := 2) (by have := s.path_len; omega)).ne
  have hgY₂ : paint₂ gY = c :=
    (hstable s.right hYmem hYneZ3 gY hgYF hgYY).trans hgYC
  have hgZ₂ : paint₂ gZ = c :=
    (hstable (s.path.1.getVert 2) hZ2mem hZ2neZ3
      gZ hgZF hgZZ2).trans hgZC
  have hcne := FivePathState.external_endpoint_color_ne_missing
    G u (by simpa [huL] using hZ3Ext)
      (by simpa [huR] using hYExt)
  obtain ⟨g₀,hg₀F,hg₀L,hg₀1,hg₀A⟩ :=
    FivePathState.exists_first_b_edge G u
  have hab : a ≠ b := by
    intro heq
    exact (G.color_ne_of_mem_missingColorsAt
      (F.erase u.omitted) u.paint u.left b u.left_missing
      hg₀F hg₀L) (hg₀A.trans heq)
  have hg₀₂ : paint₂ g₀ = a :=
    (hother g₀ (by simpa [hg₀A] using hab)
      (by simpa [hg₀A] using hcne.2.symm)).trans hg₀A
  have hZ2neY : s.path.1.getVert 2 ≠ s.right := hYZ2.symm
  obtain ⟨gA,hgAF,hgAZ,hgAY,hgAA⟩ :=
    G.forced_outside_a_edge_of_five_critical_path
      hcritical u.omitted_mem hproper₂ u.left_ne_right
      (FivePathState.internal_vertex_ne_endpoints G u
        (by omega : 0 < 1) (by omega : 1 < 4)).1.symm
      (FivePathState.internal_vertex_ne_endpoints G u
        (by omega : 0 < 1) (by omega : 1 < 4)).2
      u.left_inc u.right_inc hcLeft haRight
      (by simpa only [List.mem_toFinset] using u.path.1.start_mem_support)
      (by simpa only [List.mem_toFinset,←hu1] using
        u.path.1.getVert_mem_support 1)
      (by simpa only [List.mem_toFinset] using u.path.1.end_mem_support)
      hZoutU hYoutU hne.symm
      hg₀F hg₀L (hu1 ▸ hg₀1) hg₀₂
      hgZF (hu1 ▸ hgZZ2) hgZOut hgZ₂
      hgYF (huR ▸ hgYY) hgYOut hgY₂
      qCA hqCard
  exact ⟨outY,outZ,hne,hYout,hZout,
    gY,gZ,gA,hgYF,hgZF,hgAF,hgYY,hgYOut,hgY₂,
    hgZZ2,hgZOut,hgZ₂,hgAY,hgAZ,hgAA⟩

end WeightedEdgeColoring.WeightedMultigraph
