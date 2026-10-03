import WeightedEdgeColoring.SubtwoOrdinaryFivePresentMiddlePairActual

/-!
# The BC circuit in the Z₂-penultimate branch
-/

namespace WeightedEdgeColoring.WeightedMultigraph

universe u
variable (G : WeightedMultigraph.{u})

/-- Two exterior segments, joined by the new `XY` and `Z₁Z₂`
`b` edges, make a BC circuit which excludes `Z₃`. -/
theorem FivePathState.exists_middle_bc_circuit_of_exterior_pair
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
    ∃ path : (G.twoColorGraph (F.erase u.omitted) u.paint b c).Path
        (s.path.1.getVert 1) (s.path.1.getVert 2),
      2 ≤ path.1.length ∧
      (G.twoColorGraph (F.erase u.omitted) u.paint b c).Adj
        (s.path.1.getVert 1) (s.path.1.getVert 2) ∧
      s.path.1.getVert 3 ∉ path.1.support ∧
      ∃ circuit : (G.twoColorGraph (F.erase u.omitted) u.paint b c).Walk
          (s.path.1.getVert 2) (s.path.1.getVert 2),
        circuit.IsCycle ∧
          s.path.1.getVert 3 ∉ circuit.support := by
  classical
  let H := G.twoColorGraph (F.erase u.omitted) u.paint b c
  obtain ⟨g₁,_,g₃,hg₁F,hg₁1,hg₁2,hg₁B,
    _,_,_,_,hg₃F,hg₃3,hg₃R,hg₃B⟩ :=
    FivePathState.exists_three_surviving_path_edges G u
  have hZ12 : s.path.1.getVert 1 ≠ s.path.1.getVert 2 :=
    (s.path.1.adj_getVert_succ
      (i := 1) (by have := s.path_len; omega)).ne
  have hXY : s.left ≠ s.right := s.left_ne_right
  have h12 : H.Adj (s.path.1.getVert 1) (s.path.1.getVert 2) := by
    apply G.twoColorGraph_adj_of_witness_inc hZ12
      hg₁F (hu2 ▸ hg₁2) (hu1 ▸ hg₁1)
    exact Or.inl hg₁B
  have hYX : H.Adj s.right s.left := by
    apply G.twoColorGraph_adj_of_witness_inc hXY.symm
      hg₃F (huRight ▸ hg₃R) (hu3 ▸ hg₃3)
    exact Or.inl hg₃B
  have hZ2neY : s.path.1.getVert 2 ≠ s.right :=
    (FivePathState.internal_vertex_ne_endpoints G s
      (by omega : 0 < 2) (by omega : 2 < 4)).2
  have hZ2neZ1 : s.path.1.getVert 2 ≠ s.path.1.getVert 1 := hZ12.symm
  have hZ1neX : s.path.1.getVert 1 ≠ s.left :=
    (FivePathState.internal_vertex_ne_endpoints G s
      (by omega : 0 < 1) (by omega : 1 < 4)).1
  have hZ1neZ2 : s.path.1.getVert 1 ≠ s.path.1.getVert 2 := hZ12
  have hZ3neZ2 : s.path.1.getVert 3 ≠ s.path.1.getVert 2 :=
    (s.path.1.adj_getVert_succ
      (i := 2) (by have := s.path_len; omega)).ne.symm
  have hZ3neX : s.path.1.getVert 3 ≠ s.left :=
    (FivePathState.internal_vertex_ne_endpoints G s
      (by omega : 0 < 3) (by omega : 3 < 4)).1
  have hZ3neY : s.path.1.getVert 3 ≠ s.right :=
    (FivePathState.internal_vertex_ne_endpoints G s
      (by omega : 0 < 3) (by omega : 3 < 4)).2
  have hZ2notPre : s.path.1.getVert 2 ∉ qpre.1.support := by
    intro hm
    have hOld : s.path.1.getVert 2 ∈ s.path.1.support :=
      s.path.1.getVert_mem_support 2
    rcases hpreCap _ hm hOld with hY | hZ1
    · exact hZ2neY hY
    · exact hZ2neZ1 hZ1
  have hZ1notSuf : s.path.1.getVert 1 ∉ qsuf.1.support := by
    intro hm
    have hOld : s.path.1.getVert 1 ∈ s.path.1.support :=
      s.path.1.getVert_mem_support 1
    rcases hsufCap _ hm hOld with hX | hZ2
    · exact hZ1neX hX
    · exact hZ1neZ2 hZ2
  let walk : H.Walk (s.path.1.getVert 1) (s.path.1.getVert 2) :=
    (qpre.reverse.1.concat hYX).append qsuf.1
  have hno12Walk : s(s.path.1.getVert 1,s.path.1.getVert 2) ∉
      walk.edges := by
    intro hmem
    simp only [walk,SimpleGraph.Walk.edges_append,
      SimpleGraph.Walk.edges_concat,
      SimpleGraph.Walk.edges_reverse,List.concat_eq_append,
      List.mem_append,List.mem_singleton,List.mem_reverse] at hmem
    rcases hmem with (hPre | hYXedge) | hSuf
    · have hPre' : s(s.path.1.getVert 1,s.path.1.getVert 2) ∈
          qpre.1.edges := by
        change s(s.path.1.getVert 1,s.path.1.getVert 2) ∈
          qpre.1.reverse.edges at hPre
        simpa only [SimpleGraph.Walk.edges_reverse,
          List.mem_reverse] using hPre
      exact hZ2notPre (qpre.1.snd_mem_support_of_mem_edges hPre')
    · have hends := Sym2.eq_iff.mp hYXedge
      rcases hends with ⟨h1,_⟩ | ⟨h1,_⟩
      · exact (FivePathState.internal_vertex_ne_endpoints G s
          (by omega : 0 < 1) (by omega : 1 < 4)).2 h1
      · exact hZ1neX h1
    · exact hZ1notSuf (qsuf.1.fst_mem_support_of_mem_edges hSuf)
  let path : H.Path (s.path.1.getVert 1) (s.path.1.getVert 2) :=
    walk.toPath
  have hno12Path : s(s.path.1.getVert 1,s.path.1.getVert 2) ∉
      path.1.edges := by
    intro hmem
    exact hno12Walk (walk.edges_toPath_subset hmem)
  have hZ3notWalk : s.path.1.getVert 3 ∉ walk.support := by
    intro hmem
    have hparts : s.path.1.getVert 3 ∈
        (qpre.reverse.1.concat hYX).support ∨
        s.path.1.getVert 3 ∈ qsuf.1.support := by
      simpa only [walk,SimpleGraph.Walk.mem_support_append_iff] using hmem
    rcases hparts with hfirst | hlast
    · have hparts' : s.path.1.getVert 3 ∈ qpre.1.support ∨
          s.path.1.getVert 3 = s.left := by
        simpa [SimpleGraph.Walk.support_concat,
          SimpleGraph.Walk.support_reverse,List.concat_eq_append] using hfirst
      rcases hparts' with hpre | hX
      · exact hZ3outPre hpre
      · exact hZ3neX hX
    · exact hZ3outSuf hlast
  have hZ3notPath : s.path.1.getVert 3 ∉ path.1.support := by
    intro hmem
    exact hZ3notWalk (walk.support_toPath_subset hmem)
  let circuit : H.Walk (s.path.1.getVert 2) (s.path.1.getVert 2) :=
    .cons h12.symm path.1
  have hcycle : circuit.IsCycle := path.cons_isCycle h12.symm
    (by simpa [Sym2.eq_swap] using hno12Path)
  have hlen : 2 ≤ path.1.length := by
    have hthree := SimpleGraph.Walk.IsCycle.three_le_length hcycle
    simp only [circuit,SimpleGraph.Walk.length_cons] at hthree
    omega
  have hZ3notCircuit : s.path.1.getVert 3 ∉ circuit.support := by
    intro hmem
    simp only [circuit,SimpleGraph.Walk.support_cons,List.mem_cons] at hmem
    rcases hmem with hZ2 | hPath
    · exact hZ3neZ2 hZ2
    · exact hZ3notPath hPath
  exact ⟨path,hlen,h12,hZ3notPath,circuit,hcycle,hZ3notCircuit⟩

end WeightedEdgeColoring.WeightedMultigraph
