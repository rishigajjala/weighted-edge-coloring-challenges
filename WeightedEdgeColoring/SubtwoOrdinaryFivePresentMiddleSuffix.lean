import WeightedEdgeColoring.SubtwoOrdinaryFivePresentMiddleNoChord

/-!
# The exterior segment from X to Z₂ in the penultimate-order branch
-/

namespace WeightedEdgeColoring.WeightedMultigraph

universe u
variable (G : WeightedMultigraph.{u})

theorem FivePathState.exists_middle_exterior_suffix
    {F : Finset G.E} {k : ℕ} {a b c : Fin k}
    (s : G.FivePathState F k a b)
    (q : (G.twoColorGraph (F.erase s.omitted) s.paint b c).Path
      s.right (s.path.1.getVert 3))
    (i : ℕ)
    (hZ1 : q.1.getVert i = s.path.1.getVert 1)
    (hX : q.1.getVert (i+1) = s.left)
    (hZ2 : q.1.getVert (q.1.length-1) = s.path.1.getVert 2)
    (horder : i+1 < q.1.length-1)
    (hXmem : s.left ∈ q.1.support) :
    ∃ r : (G.twoColorGraph (F.erase s.omitted) s.paint b c).Path
        s.left (s.path.1.getVert 2),
      (∀ v ∈ r.1.support,
        v ∈ s.path.1.support →
          v = s.left ∨ v = s.path.1.getVert 2) ∧
      s.path.1.getVert 3 ∉ r.1.support ∧
      (∀ v ∈ r.1.support,
        v ∈ (q.1.takeUntil s.left hXmem).support → v = s.left) := by
  classical
  let H := G.twoColorGraph (F.erase s.omitted) s.paint b c
  let pre : H.Path s.right s.left :=
    ⟨q.1.takeUntil s.left hXmem,q.property.takeUntil hXmem⟩
  let post : H.Path s.left (s.path.1.getVert 3) :=
    ⟨q.1.dropUntil s.left hXmem,q.property.dropUntil hXmem⟩
  have hpreLen : pre.1.length = i+1 := by
    have hget := q.1.getVert_length_takeUntil hXmem
    have hlen := q.1.length_takeUntil_le hXmem
    exact q.property.getVert_injOn
      (Set.mem_Iic.mpr hlen)
      (Set.mem_Iic.mpr (by omega : i+1 ≤ q.1.length))
      (hget.trans hX.symm)
  have hZ1pre : s.path.1.getVert 1 ∈ pre.1.support := by
    have hget : pre.1.getVert i = s.path.1.getVert 1 := by
      exact (q.1.getVert_takeUntil hXmem (by omega : i ≤ pre.1.length)).trans hZ1
    exact hget ▸ pre.1.getVert_mem_support i
  have hYpre : s.right ∈ pre.1.support := pre.1.start_mem_support
  have hZ2q : s.path.1.getVert 2 ∈ q.1.support := by
    exact hZ2 ▸ q.1.getVert_mem_support (q.1.length-1)
  have hZ2notPre : s.path.1.getVert 2 ∉ pre.1.support := by
    intro hmem
    obtain ⟨j,hj,hjLe⟩ :=
      SimpleGraph.Walk.mem_support_iff_exists_getVert.mp hmem
    have hjQ : q.1.getVert j = s.path.1.getVert 2 :=
      (q.1.getVert_takeUntil hXmem hjLe).symm.trans hj
    have hinj := q.property.getVert_injOn
      (Set.mem_Iic.mpr (by omega : j ≤ q.1.length))
      (Set.mem_Iic.mpr (by omega : q.1.length-1 ≤ q.1.length))
      (hjQ.trans hZ2.symm)
    omega
  have hZ2post : s.path.1.getVert 2 ∈ post.1.support := by
    have hQ : q.1 = pre.1.append post.1 :=
      (q.1.take_spec hXmem).symm
    have hUnion : s.path.1.getVert 2 ∈ pre.1.support ∨
        s.path.1.getVert 2 ∈ post.1.support := by
      rw [hQ, SimpleGraph.Walk.mem_support_append_iff] at hZ2q
      exact hZ2q
    exact hUnion.resolve_left hZ2notPre
  let r : H.Path s.left (s.path.1.getVert 2) :=
    ⟨post.1.takeUntil (s.path.1.getVert 2) hZ2post,
      post.property.takeUntil hZ2post⟩
  have hZ3neZ2 : s.path.1.getVert 3 ≠ s.path.1.getVert 2 :=
    (s.path.1.adj_getVert_succ
      (i := 2) (by have := s.path_len; omega)).ne.symm
  have hZ3notR : s.path.1.getVert 3 ∉ r.1.support := by
    intro hmem
    have hpostEq : post.1 =
        r.1.append (post.1.dropUntil (s.path.1.getVert 2) hZ2post) := by
      exact (post.1.take_spec hZ2post).symm
    have htailMem : s.path.1.getVert 3 ∈
        (post.1.dropUntil (s.path.1.getVert 2) hZ2post).support :=
      (post.1.dropUntil (s.path.1.getVert 2) hZ2post).end_mem_support
    have hpath : (r.1.append
        (post.1.dropUntil (s.path.1.getVert 2) hZ2post)).IsPath := by
      rw [← hpostEq]
      exact post.property
    have hne := SimpleGraph.Walk.IsPath.ne_of_mem_support_of_append
      hpath hZ3neZ2 hmem htailMem
    exact hne rfl
  refine ⟨r, ?_, hZ3notR, ?_⟩
  · intro v hv hvS
    have hvOld : v ∈ s.path.1.support.toFinset := by simpa using hvS
    rw [FivePathState.support_eq_five_vertices G s] at hvOld
    simp only [Finset.mem_insert,Finset.mem_singleton] at hvOld
    have hvPost : v ∈ post.1.support :=
      SimpleGraph.Walk.support_takeUntil_subset post.1 hZ2post hv
    have hpostEq : q.1 = pre.1.append post.1 := by
      exact (q.1.take_spec hXmem).symm
    have hqPath : (pre.1.append post.1).IsPath := by
      rw [← hpostEq]
      exact q.property
    have hYneX : s.right ≠ s.left := s.left_ne_right.symm
    have hZ1neX : s.path.1.getVert 1 ≠ s.left :=
      (FivePathState.internal_vertex_ne_endpoints G s
        (by omega : 0 < 1) (by omega : 1 < 4)).1
    have hYnotPost : s.right ∉ post.1.support := by
      intro hmem
      have hne := SimpleGraph.Walk.IsPath.ne_of_mem_support_of_append
        hqPath hYneX hYpre hmem
      exact hne rfl
    have hZ1notPost : s.path.1.getVert 1 ∉ post.1.support := by
      intro hmem
      have hne := SimpleGraph.Walk.IsPath.ne_of_mem_support_of_append
        hqPath hZ1neX hZ1pre hmem
      exact hne rfl
    rcases hvOld with hX | hZ1 | hZ2 | hZ3 | hY
    · exact Or.inl hX
    · exact False.elim (hZ1notPost (hZ1 ▸ hvPost))
    · exact Or.inr hZ2
    · exact False.elim (hZ3notR (hZ3 ▸ hv))
    · exact False.elim (hYnotPost (hY ▸ hvPost))
  · intro v hv hvPre
    by_contra hvNeX
    have hvPost : v ∈ post.1.support :=
      SimpleGraph.Walk.support_takeUntil_subset post.1 hZ2post hv
    have hqPath : (pre.1.append post.1).IsPath := by
      rw [← (q.1.take_spec hXmem).symm]
      exact q.property
    have hne := SimpleGraph.Walk.IsPath.ne_of_mem_support_of_append
      hqPath hvNeX hvPre hvPost
    exact hne rfl

end WeightedEdgeColoring.WeightedMultigraph
