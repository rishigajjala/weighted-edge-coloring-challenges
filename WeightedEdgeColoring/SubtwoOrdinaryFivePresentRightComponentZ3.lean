import WeightedEdgeColoring.SubtwoOrdinaryFivePresentFirstReturnAnyTarget

/-!
# The right two-color component cannot reach the old third vertex
-/

namespace WeightedEdgeColoring.WeightedMultigraph

universe u
variable (G : WeightedMultigraph.{u})

theorem FivePathState.false_of_right_bc_component_reaches_z3
    {F : Finset G.E} {k D : ℕ} {a b c : Fin k}
    (s : G.FivePathState F k a b)
    (hcritical : G.IsColorCriticalOn F k)
    (hdk : D + 1 < k) (hdegree : ∀ z, G.degreeOn F z ≤ D)
    (hthreshold : 7 * D < 6 * k + 2)
    (hnot : FivePathState.NotTwoInternalColor G s c)
    (hleft : FivePathState.HasExternalColorAt G s c s.left)
    (hright : FivePathState.HasExternalColorAt G s c s.right)
    (hseparate : (G.twoColorGraph (F.erase s.omitted) s.paint b c).connectedComponentMk
        s.left ≠
      (G.twoColorGraph (F.erase s.omitted) s.paint b c).connectedComponentMk
        s.right)
    (hZ3comp : (G.twoColorGraph (F.erase s.omitted) s.paint b c).connectedComponentMk
        (s.path.1.getVert 3) =
      (G.twoColorGraph (F.erase s.omitted) s.paint b c).connectedComponentMk
        s.right) : False := by
  classical
  let H := G.twoColorGraph (F.erase s.omitted) s.paint b c
  have hreach : H.Reachable s.right (s.path.1.getVert 3) :=
    SimpleGraph.ConnectedComponent.exact hZ3comp.symm
  obtain ⟨walk⟩ := hreach
  let p : H.Path s.right (s.path.1.getVert 3) := walk.toPath
  let S := s.path.1.support.toFinset
  let P : ℕ → Prop := fun i ↦
    0 < i ∧ i ≤ p.1.length ∧ p.1.getVert i ∈ S
  have hZ3S : s.path.1.getVert 3 ∈ S := by
    simpa [S] using s.path.1.getVert_mem_support 3
  have hlen : 0 < p.1.length := by
    by_contra h
    have hz : p.1.length = 0 := by omega
    have heq := SimpleGraph.Walk.eq_of_length_eq_zero hz
    exact (FivePathState.internal_vertex_ne_endpoints G s
      (by omega : 0 < 3) (by omega : 3 < 4)).2 heq.symm
  have hP : ∃ i, P i := by
    refine ⟨p.1.length, hlen, le_refl _, ?_⟩
    simpa only [p.1.getVert_length] using hZ3S
  let i := Nat.find hP
  have hiP : P i := Nat.find_spec hP
  have hi : 1 < i := by
    have hpos : 0 < i := hiP.1
    by_contra h
    have hi1 : i = 1 := by omega
    have hV : p.1.getVert 1 ∈ S := hi1 ▸ hiP.2.2
    have hadj : H.Adj s.right (p.1.getVert 1) := by
      simpa using p.1.adj_getVert_succ (i := 0) (by omega)
    exact (FivePathState.no_right_bc_adj_old_vertex G s hright hV) hadj
  have hiLe : i ≤ p.1.length := hiP.2.1
  have hfirst : ∀ j, 0 < j → j < i →
      p.1.getVert j ∉ S := by
    intro j hj hji hjS
    exact (Nat.find_min hP hji) ⟨hj,by omega,hjS⟩
  have hcase : p.1.getVert i = s.path.1.getVert 1 ∨
      p.1.getVert i = s.path.1.getVert 2 ∨
      p.1.getVert i = s.path.1.getVert 3 := by
    have hverts := FivePathState.support_eq_five_vertices G s
    have hiS : p.1.getVert i ∈ s.path.1.support.toFinset := hiP.2.2
    rw [hverts] at hiS
    simp only [Finset.mem_insert, Finset.mem_singleton] at hiS
    rcases hiS with hX | h1 | h2 | h3 | hY
    · have hcomp : H.connectedComponentMk (p.1.getVert i) =
          H.connectedComponentMk s.right :=
        (SimpleGraph.ConnectedComponent.sound
          ⟨p.1.takeUntil (p.1.getVert i)
            (p.1.getVert_mem_support i)⟩).symm
      exact False.elim (hseparate (hX ▸ hcomp))
    · exact Or.inl h1
    · exact Or.inr (Or.inl h2)
    · exact Or.inr (Or.inr h3)
    · have hidx := p.property.getVert_injOn
        (Set.mem_Iic.mpr hiLe)
        (Set.mem_Iic.mpr (by omega : 0 ≤ p.1.length))
        (by simpa [hY] using p.1.getVert_zero.symm)
      exact False.elim (by omega)
  obtain ⟨g₀,hg₀F,hg₀X,hg₀1,hg₀B⟩ :=
    FivePathState.exists_first_b_edge G s
  obtain ⟨_,g₂,_,_,_,_,_,hg₂F,hg₂2,hg₂3,hg₂B,_,_,_,_⟩ :=
    FivePathState.exists_three_surviving_path_edges G s
  have hS0 : s.left ∈ S := by simpa [S] using s.path.1.start_mem_support
  have hS2 : s.path.1.getVert 2 ∈ S := by
    simpa [S] using s.path.1.getVert_mem_support 2
  have hS3 : s.path.1.getVert 3 ∈ S := by
    simpa [S] using s.path.1.getVert_mem_support 3
  rcases hcase with h1 | h2 | h3
  · have hcompY1 : H.connectedComponentMk s.right =
        H.connectedComponentMk (s.path.1.getVert 1) :=
      SimpleGraph.ConnectedComponent.sound
        ⟨p.1.takeUntil (s.path.1.getVert 1)
          (h1 ▸ p.1.getVert_mem_support i)⟩
    have hcomp1X : H.connectedComponentMk (s.path.1.getVert 1) =
        H.connectedComponentMk s.left :=
      SimpleGraph.ConnectedComponent.connectedComponentMk_eq_of_adj
        (G.twoColorGraph_adj_of_witness_inc
          (FivePathState.internal_vertex_ne_endpoints G s
            (by omega : 0 < 1) (by omega : 1 < 4)).1.symm
          hg₀F hg₀X hg₀1 (Or.inl hg₀B)).symm
    exact hseparate (hcomp1X.symm.trans hcompY1.symm)
  · have hZ2 : FivePathState.HasExternalColorAt G s c
        (s.path.1.getVert 2) := by
      apply h2 ▸ FivePathState.external_color_at_first_return_of_internal_b_edge_any_target
        G s p hi hiLe hfirst hg₂F (h2 ▸ hg₂2) hg₂3
        (h2 ▸ (s.path.1.adj_getVert_succ
          (i := 2) (by have := s.path_len; omega)).ne)
        hS3 hg₂B
    exact FivePathState.false_of_middle_first_z2
      G s hcritical hdk hdegree hthreshold hnot
        hleft hright hZ2 p hi hiLe hfirst h2
  · have hZ3 : FivePathState.HasExternalColorAt G s c
        (s.path.1.getVert 3) := by
      have hne := (s.path.1.adj_getVert_succ
        (i := 2) (by have := s.path_len; omega)).ne
      have hExt := FivePathState.external_color_at_first_return_of_internal_b_edge_any_target
        G s p hi hiLe hfirst hg₂F (h3.symm ▸ hg₂3) hg₂2
        (h3.symm ▸ hne.symm) hS2 hg₂B
      simpa only [h3] using hExt
    exact FivePathState.false_of_middle_first_z3
      G s hcritical hdk hdegree hthreshold
        hleft hright hZ3 p hi hiLe hfirst h3

end WeightedEdgeColoring.WeightedMultigraph
