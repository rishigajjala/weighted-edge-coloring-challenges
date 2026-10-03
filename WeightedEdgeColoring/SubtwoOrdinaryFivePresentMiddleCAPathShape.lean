import WeightedEdgeColoring.SubtwoOrdinaryFivePresentMiddleForcedOutsideActual

/-!
# Exact support of the second switched critical CA path
-/

namespace WeightedEdgeColoring.WeightedMultigraph

universe u
variable (G : WeightedMultigraph.{u})

theorem FivePathState.middle_ca_path_support_of_exterior_edges
    {F : Finset G.E} {k : ℕ} {a b c : Fin k}
    (u : G.FivePathState F k b a)
    (hcritical : G.IsColorCriticalOn F k)
    {paint₂ : G.E → Fin k}
    (hproper₂ : G.IsProperOn (F.erase u.omitted) paint₂)
    (hcLeft : c ∈ G.missingColorsAt (F.erase u.omitted) paint₂ u.left)
    (haRight : a ∈ G.missingColorsAt (F.erase u.omitted) paint₂ u.right)
    {outY outZ : G.V}
    (hne : outY ≠ outZ)
    (hYout : outY ∉ u.path.1.support.toFinset)
    (hZout : outZ ∉ u.path.1.support.toFinset)
    {g₀ gY gZ : G.E}
    (hg₀F : g₀ ∈ F.erase u.omitted)
    (hg₀L : G.Inc u.left g₀)
    (hg₀1 : G.Inc (u.path.1.getVert 1) g₀)
    (hg₀A : paint₂ g₀ = a)
    (hgYF : gY ∈ F.erase u.omitted)
    (hgYY : G.Inc u.right gY) (hgYOut : G.Inc outY gY)
    (hgYC : paint₂ gY = c)
    (hgZF : gZ ∈ F.erase u.omitted)
    (hgZ1 : G.Inc (u.path.1.getVert 1) gZ)
    (hgZOut : G.Inc outZ gZ)
    (hgZC : paint₂ gZ = c)
    (qCA : (G.twoColorGraph (F.erase u.omitted) paint₂ c a).Path
      u.left u.right)
    (hqCard : qCA.1.support.toFinset.card ≤ 5) :
    qCA.1.support.toFinset =
      {u.left,u.path.1.getVert 1,outZ,outY,u.right} := by
  let H := G.twoColorGraph (F.erase u.omitted) paint₂ c a
  have hLZ : u.left ≠ u.path.1.getVert 1 :=
    (FivePathState.internal_vertex_ne_endpoints G u
      (by omega : 0 < 1) (by omega : 1 < 4)).1.symm
  have hZY : u.path.1.getVert 1 ≠ u.right :=
    (FivePathState.internal_vertex_ne_endpoints G u
      (by omega : 0 < 1) (by omega : 1 < 4)).2
  have hLoutZ : u.left ≠ outZ := by
    intro heq
    exact hZout (heq ▸ (by simpa only [List.mem_toFinset] using
      u.path.1.start_mem_support))
  have hZoutZ : u.path.1.getVert 1 ≠ outZ := by
    intro heq
    exact hZout (heq ▸ (by simpa only [List.mem_toFinset] using
      u.path.1.getVert_mem_support 1))
  have hYoutZ : u.right ≠ outZ := by
    intro heq
    exact hZout (heq ▸ (by simpa only [List.mem_toFinset] using
      u.path.1.end_mem_support))
  have hLoutY : u.left ≠ outY := by
    intro heq
    exact hYout (heq ▸ (by simpa only [List.mem_toFinset] using
      u.path.1.start_mem_support))
  have hZoutY : u.path.1.getVert 1 ≠ outY := by
    intro heq
    exact hYout (heq ▸ (by simpa only [List.mem_toFinset] using
      u.path.1.getVert_mem_support 1))
  have hYoutY : u.right ≠ outY := by
    intro heq
    exact hYout (heq ▸ (by simpa only [List.mem_toFinset] using
      u.path.1.end_mem_support))
  have hAdjLZ : H.Adj u.left (u.path.1.getVert 1) :=
    G.twoColorGraph_adj_of_witness_inc hLZ
      hg₀F hg₀L hg₀1 (Or.inr hg₀A)
  have hAdjZOut : H.Adj (u.path.1.getVert 1) outZ :=
    G.twoColorGraph_adj_of_witness_inc hZoutZ
      hgZF hgZ1 hgZOut (Or.inl hgZC)
  have hAdjYOut : H.Adj u.right outY :=
    G.twoColorGraph_adj_of_witness_inc hYoutY
      hgYF hgYY hgYOut (Or.inl hgYC)
  have hcompLY := G.critical_endpoints_same_twoColorComponent_at
    hcritical u.omitted_mem hproper₂ u.left_ne_right
      u.left_inc u.right_inc hcLeft haRight
  have hcompLZ := SimpleGraph.ConnectedComponent.connectedComponentMk_eq_of_adj hAdjLZ
  have hcompZOut := SimpleGraph.ConnectedComponent.connectedComponentMk_eq_of_adj hAdjZOut
  have hcompYOut := SimpleGraph.ConnectedComponent.connectedComponentMk_eq_of_adj hAdjYOut
  have hZcomp : H.connectedComponentMk (u.path.1.getVert 1) =
      H.connectedComponentMk u.left := hcompLZ.symm
  have hOutZcomp : H.connectedComponentMk outZ =
      H.connectedComponentMk u.left := hcompZOut.symm.trans hZcomp
  have hOutYcomp : H.connectedComponentMk outY =
      H.connectedComponentMk u.left := hcompYOut.symm.trans hcompLY.symm
  have hZmem : u.path.1.getVert 1 ∈ qCA.1.support :=
    G.mem_criticalPath_support_of_same_twoColorComponent_at
      hcritical u.omitted_mem hproper₂ u.left_ne_right
      u.left_inc u.right_inc hcLeft haRight qCA hZcomp
  have hOutZmem : outZ ∈ qCA.1.support :=
    G.mem_criticalPath_support_of_same_twoColorComponent_at
      hcritical u.omitted_mem hproper₂ u.left_ne_right
      u.left_inc u.right_inc hcLeft haRight qCA hOutZcomp
  have hOutYmem : outY ∈ qCA.1.support :=
    G.mem_criticalPath_support_of_same_twoColorComponent_at
      hcritical u.omitted_mem hproper₂ u.left_ne_right
      u.left_inc u.right_inc hcLeft haRight qCA hOutYcomp
  exact G.five_path_support_eq_of_five_members
    qCA hqCard hZmem hOutZmem hOutYmem
    hLZ u.left_ne_right hZY
    hLoutZ.symm hZoutZ.symm hYoutZ.symm
    hLoutY.symm hZoutY.symm hYoutY.symm
    hne.symm

end WeightedEdgeColoring.WeightedMultigraph
