import WeightedEdgeColoring.SubtwoOrdinaryFivePresentMiddleCircuitActual

/-!
# Route around the BC circuit from Y to X, avoiding the direct XY edge
-/

namespace WeightedEdgeColoring.WeightedMultigraph

universe u
variable (G : WeightedMultigraph.{u})

theorem FivePathState.exists_middle_bc_route_avoiding_xy
    {F : Finset G.E} {k : ℕ} {a b c : Fin k}
    (s : G.FivePathState F k a b)
    (u : G.FivePathState F k b a)
    (hu1 : u.path.1.getVert 1 = s.path.1.getVert 2)
    (hu2 : u.path.1.getVert 2 = s.path.1.getVert 1)
    (hu3 : u.path.1.getVert 3 = s.left)
    (huRight : u.right = s.right)
    (qpre : (G.twoColorGraph (F.erase u.omitted) u.paint b c).Path
      s.right (s.path.1.getVert 1))
    (qsuf : (G.twoColorGraph (F.erase u.omitted) u.paint b c).Path
      s.left (s.path.1.getVert 2))
    (hpreCap : ∀ v ∈ qpre.1.support,
      v ∈ s.path.1.support →
        v = s.right ∨ v = s.path.1.getVert 1)
    (hsufCap : ∀ v ∈ qsuf.1.support,
      v ∈ s.path.1.support →
        v = s.left ∨ v = s.path.1.getVert 2)
    (hZ3outPre : s.path.1.getVert 3 ∉ qpre.1.support)
    (hZ3outSuf : s.path.1.getVert 3 ∉ qsuf.1.support) :
    ∃ route : (G.twoColorGraph (F.erase u.omitted) u.paint b c).Path
        s.right s.left,
      2 ≤ route.1.length ∧
      (G.twoColorGraph (F.erase u.omitted) u.paint b c).Adj
        s.left s.right ∧
      s.path.1.getVert 3 ∉ route.1.support := by
  classical
  let H := G.twoColorGraph (F.erase u.omitted) u.paint b c
  obtain ⟨g₁,_,g₃,hg₁F,hg₁1,hg₁2,hg₁B,
    _,_,_,_,hg₃F,hg₃3,hg₃R,hg₃B⟩ :=
    FivePathState.exists_three_surviving_path_edges G u
  have hZ12 : s.path.1.getVert 1 ≠ s.path.1.getVert 2 :=
    (s.path.1.adj_getVert_succ
      (i := 1) (by have := s.path_len; omega)).ne
  have h12 : H.Adj (s.path.1.getVert 1) (s.path.1.getVert 2) := by
    apply G.twoColorGraph_adj_of_witness_inc hZ12
      hg₁F (hu2 ▸ hg₁2) (hu1 ▸ hg₁1)
    exact Or.inl hg₁B
  have hYX : H.Adj s.right s.left := by
    apply G.twoColorGraph_adj_of_witness_inc s.left_ne_right.symm
      hg₃F (huRight ▸ hg₃R) (hu3 ▸ hg₃3)
    exact Or.inl hg₃B
  have hXnotPre : s.left ∉ qpre.1.support := by
    intro hm
    rcases hpreCap _ hm s.path.1.start_mem_support with hY | hZ1
    · exact s.left_ne_right hY
    · exact (FivePathState.internal_vertex_ne_endpoints G s
        (by omega : 0 < 1) (by omega : 1 < 4)).1 hZ1.symm
  have hYnotSuf : s.right ∉ qsuf.1.support := by
    intro hm
    rcases hsufCap _ hm s.path.1.end_mem_support with hX | hZ2
    · exact s.left_ne_right hX.symm
    · exact (FivePathState.internal_vertex_ne_endpoints G s
        (by omega : 0 < 2) (by omega : 2 < 4)).2 hZ2.symm
  have hZ3neZ1 : s.path.1.getVert 3 ≠ s.path.1.getVert 1 := by
    intro heq
    have hinj := s.path.property.getVert_injOn
      (Set.mem_Iic.mpr (by have := s.path_len; omega : 3 ≤ s.path.1.length))
      (Set.mem_Iic.mpr (by have := s.path_len; omega : 1 ≤ s.path.1.length)) heq
    omega
  have hZ3neZ2 : s.path.1.getVert 3 ≠ s.path.1.getVert 2 :=
    (s.path.1.adj_getVert_succ
      (i := 2) (by have := s.path_len; omega)).ne.symm
  let walk : H.Walk s.right s.left :=
    (qpre.1.concat h12).append qsuf.reverse.1
  have hnoXYWalk : s(s.right,s.left) ∉ walk.edges := by
    intro hmem
    simp only [walk,SimpleGraph.Walk.edges_append,
      SimpleGraph.Walk.edges_concat,List.concat_eq_append,
      List.mem_append,List.mem_singleton] at hmem
    rcases hmem with (hPre | h12edge) | hSuf
    · exact hXnotPre (qpre.1.snd_mem_support_of_mem_edges hPre)
    · have hends := Sym2.eq_iff.mp h12edge
      rcases hends with ⟨h1,_⟩ | ⟨h1,_⟩
      · exact (FivePathState.internal_vertex_ne_endpoints G s
          (by omega : 0 < 1) (by omega : 1 < 4)).2 h1.symm
      · exact (FivePathState.internal_vertex_ne_endpoints G s
          (by omega : 0 < 2) (by omega : 2 < 4)).2 h1.symm
    · have hSuf' : s(s.right,s.left) ∈ qsuf.1.edges := by
        change s(s.right,s.left) ∈ qsuf.1.reverse.edges at hSuf
        simpa only [SimpleGraph.Walk.edges_reverse,List.mem_reverse] using hSuf
      exact hYnotSuf (qsuf.1.fst_mem_support_of_mem_edges hSuf')
  let route : H.Path s.right s.left := walk.toPath
  have hnoXYRoute : s(s.right,s.left) ∉ route.1.edges := by
    intro hmem
    exact hnoXYWalk (walk.edges_toPath_subset hmem)
  have hZ3notWalk : s.path.1.getVert 3 ∉ walk.support := by
    intro hmem
    have hparts : s.path.1.getVert 3 ∈
        (qpre.1.concat h12).support ∨
        s.path.1.getVert 3 ∈ qsuf.reverse.1.support := by
      simpa only [walk,SimpleGraph.Walk.mem_support_append_iff] using hmem
    rcases hparts with hfirst | hlast
    · have hparts' : s.path.1.getVert 3 ∈ qpre.1.support ∨
          s.path.1.getVert 3 = s.path.1.getVert 2 := by
        simpa [SimpleGraph.Walk.support_concat,
          List.concat_eq_append] using hfirst
      rcases hparts' with hpre | hZ2
      · exact hZ3outPre hpre
      · exact hZ3neZ2 hZ2
    · exact hZ3outSuf (by simpa [SimpleGraph.Walk.support_reverse] using hlast)
  have hZ3notRoute : s.path.1.getVert 3 ∉ route.1.support := by
    intro hmem
    exact hZ3notWalk (walk.support_toPath_subset hmem)
  have hcycle : (SimpleGraph.Walk.cons hYX.symm route.1).IsCycle :=
    route.cons_isCycle hYX.symm
      (by simpa [Sym2.eq_swap] using hnoXYRoute)
  have hlen : 2 ≤ route.1.length := by
    have hthree := SimpleGraph.Walk.IsCycle.three_le_length hcycle
    simp only [SimpleGraph.Walk.length_cons] at hthree
    omega
  exact ⟨route,hlen,hYX.symm,hZ3notRoute⟩

end WeightedEdgeColoring.WeightedMultigraph
