import WeightedEdgeColoring.SubtwoOrdinaryFivePresentVZ1DLocations

/-!
# The second nested four-vertex circuit
-/

namespace WeightedEdgeColoring.WeightedMultigraph

universe u
variable (G : WeightedMultigraph.{u})

/-- Alternating `d,b,d,b` edges on `Y,Z₁,Z₂,Z₃,Y` make a
four-cycle of the `(b,d)` graph, with `X` outside it. -/
theorem FivePathState.exists_bd_cycle_of_four_edges
    {F : Finset G.E} {k : ℕ} {a b d : Fin k}
    (s : G.FivePathState F k a b)
    {paint : G.E → Fin k}
    {gY g12 gM g3 : G.E}
    (hgYF : gY ∈ F.erase s.omitted)
    (hgYY : G.Inc s.right gY)
    (hgYZ : G.Inc (s.path.1.getVert 1) gY)
    (hgYD : paint gY = d)
    (hg12F : g12 ∈ F.erase s.omitted)
    (hg12Z1 : G.Inc (s.path.1.getVert 1) g12)
    (hg12Z2 : G.Inc (s.path.1.getVert 2) g12)
    (hg12B : paint g12 = b)
    (hgMF : gM ∈ F.erase s.omitted)
    (hgMZ2 : G.Inc (s.path.1.getVert 2) gM)
    (hgMZ3 : G.Inc (s.path.1.getVert 3) gM)
    (hgMD : paint gM = d)
    (hg3F : g3 ∈ F.erase s.omitted)
    (hg3Z3 : G.Inc (s.path.1.getVert 3) g3)
    (hg3Y : G.Inc s.right g3)
    (hg3B : paint g3 = b) :
    ∃ q : (G.twoColorGraph (F.erase s.omitted) paint b d).Path
        s.right (s.path.1.getVert 3),
      2 ≤ q.1.length ∧
      (G.twoColorGraph (F.erase s.omitted) paint b d).Adj
        (s.path.1.getVert 3) s.right ∧
      s.left ∉ q.1.support ∧
      ∃ circuit : (G.twoColorGraph (F.erase s.omitted) paint b d).Walk
          s.right s.right,
        circuit.IsCycle ∧ s.left ∉ circuit.support := by
  classical
  let H := G.twoColorGraph (F.erase s.omitted) paint b d
  have hZ1Y : s.path.1.getVert 1 ≠ s.right :=
    (FivePathState.internal_vertex_ne_endpoints G s
      (by omega : 0 < 1) (by omega : 1 < 4)).2
  have hZ2Y : s.path.1.getVert 2 ≠ s.right :=
    (FivePathState.internal_vertex_ne_endpoints G s
      (by omega : 0 < 2) (by omega : 2 < 4)).2
  have hZ3Y : s.path.1.getVert 3 ≠ s.right :=
    (FivePathState.internal_vertex_ne_endpoints G s
      (by omega : 0 < 3) (by omega : 3 < 4)).2
  have hZ12 : s.path.1.getVert 1 ≠ s.path.1.getVert 2 :=
    (s.path.1.adj_getVert_succ
      (i := 1) (by have := s.path_len; omega)).ne
  have hZ23 : s.path.1.getVert 2 ≠ s.path.1.getVert 3 :=
    (s.path.1.adj_getVert_succ
      (i := 2) (by have := s.path_len; omega)).ne
  have hZ13 : s.path.1.getVert 1 ≠ s.path.1.getVert 3 := by
    intro h
    have hinj := s.path.property.getVert_injOn
      (Set.mem_Iic.mpr (by have := s.path_len; omega : 1 ≤ s.path.1.length))
      (Set.mem_Iic.mpr (by have := s.path_len; omega : 3 ≤ s.path.1.length)) h
    omega
  have hY1 : H.Adj s.right (s.path.1.getVert 1) :=
    G.twoColorGraph_adj_of_witness_inc hZ1Y.symm
      hgYF hgYY hgYZ (Or.inr hgYD)
  have h12 : H.Adj (s.path.1.getVert 1) (s.path.1.getVert 2) :=
    G.twoColorGraph_adj_of_witness_inc hZ12
      hg12F hg12Z1 hg12Z2 (Or.inl hg12B)
  have h23 : H.Adj (s.path.1.getVert 2) (s.path.1.getVert 3) :=
    G.twoColorGraph_adj_of_witness_inc hZ23
      hgMF hgMZ2 hgMZ3 (Or.inr hgMD)
  have h3Y : H.Adj (s.path.1.getVert 3) s.right :=
    G.twoColorGraph_adj_of_witness_inc hZ3Y
      hg3F hg3Z3 hg3Y (Or.inl hg3B)
  let q0 : H.Path s.right s.right := .nil
  have hZ1notQ0 : s.path.1.getVert 1 ∉ q0.1.support := by
    simpa [q0] using hZ1Y
  let q1 : H.Path s.right (s.path.1.getVert 1) :=
    ⟨q0.1.concat hY1, q0.property.concat hZ1notQ0 hY1⟩
  have hZ2notQ1 : s.path.1.getVert 2 ∉ q1.1.support := by
    simp [q1, q0, SimpleGraph.Walk.support_concat,
      hZ2Y, hZ12.symm]
  let q2 : H.Path s.right (s.path.1.getVert 2) :=
    ⟨q1.1.concat h12, q1.property.concat hZ2notQ1 h12⟩
  have hZ3notQ2 : s.path.1.getVert 3 ∉ q2.1.support := by
    simp [q2, q1, q0, SimpleGraph.Walk.support_concat,
      hZ3Y, hZ13.symm, hZ23.symm]
  let q3 : H.Path s.right (s.path.1.getVert 3) :=
    ⟨q2.1.concat h23, q2.property.concat hZ3notQ2 h23⟩
  have hqLen : q3.1.length = 3 := by
    simp [q3, q2, q1, q0, SimpleGraph.Walk.length_concat]
  have hXnotQ3 : s.left ∉ q3.1.support := by
    have hXneY := s.left_ne_right
    have hXneZ1 := (FivePathState.internal_vertex_ne_endpoints G s
      (by omega : 0 < 1) (by omega : 1 < 4)).1.symm
    have hXneZ2 := (FivePathState.internal_vertex_ne_endpoints G s
      (by omega : 0 < 2) (by omega : 2 < 4)).1.symm
    have hXneZ3 := (FivePathState.internal_vertex_ne_endpoints G s
      (by omega : 0 < 3) (by omega : 3 < 4)).1.symm
    simp [q3, q2, q1, q0, SimpleGraph.Walk.support_concat,
      hXneY, hXneZ1, hXneZ2, hXneZ3]
  have hnoClose : s(s.right, s.path.1.getVert 3) ∉ q3.1.edges := by
    intro hmem
    have hYpen := q3.property.eq_penultimate_of_mem_edges
      (by simpa [Sym2.eq_swap] using hmem :
        s(s.path.1.getVert 3, s.right) ∈ q3.1.edges)
    have hpen : q3.1.penultimate = s.path.1.getVert 2 := by
      simp [q3, SimpleGraph.Walk.penultimate_concat]
    exact hZ2Y.symm (hYpen.trans hpen)
  let qR : H.Path (s.path.1.getVert 3) s.right := q3.reverse
  have hnoCloseR : s(s.right, s.path.1.getVert 3) ∉ qR.1.edges := by
    intro hmem
    apply hnoClose
    simpa [qR, SimpleGraph.Walk.edges_reverse] using hmem
  let circuit : H.Walk s.right s.right := .cons h3Y.symm qR.1
  have hcycle : circuit.IsCycle :=
    qR.cons_isCycle h3Y.symm hnoCloseR
  have hXnotCircuit : s.left ∉ circuit.support := by
    intro h
    simp only [circuit, SimpleGraph.Walk.support_cons,
      List.mem_cons] at h
    rcases h with hEq | hMem
    · exact s.left_ne_right hEq
    · exact hXnotQ3 (by simpa [qR] using hMem)
  exact ⟨q3, by omega, h3Y, hXnotQ3,
    circuit, hcycle, hXnotCircuit⟩

end WeightedEdgeColoring.WeightedMultigraph
