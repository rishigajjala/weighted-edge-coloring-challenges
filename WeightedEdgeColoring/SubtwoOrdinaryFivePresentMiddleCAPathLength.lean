import WeightedEdgeColoring.SubtwoOrdinaryFivePresentMiddleDSharedEdge

/-!
# Four-edge length of the forced critical CA path
-/

namespace WeightedEdgeColoring.WeightedMultigraph

universe u
variable (G : WeightedMultigraph.{u})

theorem FivePathState.middle_ca_path_length_of_support
    {F : Finset G.E} {k : ℕ} {a b c : Fin k}
    (u : G.FivePathState F k b a)
    {paint₂ : G.E → Fin k}
    {outY outZ : G.V}
    (hne : outY ≠ outZ)
    (hYout : outY ∉ u.path.1.support.toFinset)
    (hZout : outZ ∉ u.path.1.support.toFinset)
    (qCA : (G.twoColorGraph (F.erase u.omitted) paint₂ c a).Path
      u.left u.right)
    (hqSupport : qCA.1.support.toFinset =
      {u.left,u.path.1.getVert 1,outZ,outY,u.right}) :
    qCA.1.length = 4 := by
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
  have hnodup : [u.left,u.path.1.getVert 1,outZ,outY,u.right].Nodup := by
    simp [u.left_ne_right,hLZ,hZY,hLoutZ,hZoutZ,hYoutZ.symm,
      hLoutY,hZoutY,hYoutY.symm,hne.symm]
  have heq : ([u.left,u.path.1.getVert 1,outZ,outY,u.right] : List G.V).toFinset =
      ({u.left,u.path.1.getVert 1,outZ,outY,u.right} : Finset G.V) := by
    ext v
    simp
  have hcard : qCA.1.support.toFinset.card = 5 := by
    rw [hqSupport,←heq,List.toFinset_card_of_nodup hnodup]
    simp
  have hsupportCard : qCA.1.support.toFinset.card = qCA.1.length+1 := by
    rw [List.toFinset_card_of_nodup qCA.property.support_nodup,
      qCA.1.length_support]
  omega

end WeightedEdgeColoring.WeightedMultigraph
