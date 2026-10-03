import WeightedEdgeColoring.SubtwoOrdinaryFivePresentMiddleFirstPrefix

/-!
# The middle-first cross-chord forces a switched two-color circuit
-/

namespace WeightedEdgeColoring.WeightedMultigraph

universe u
variable (G : WeightedMultigraph.{u})

theorem FivePathState.exists_middle_first_cross_chord_circuit
    {F : Finset G.E} {k : ℕ} {a b c : Fin k}
    (s : G.FivePathState F k a b)
    (hcritical : G.IsColorCriticalOn F k)
    (hleft : FivePathState.HasExternalColorAt G s c s.left)
    (hright : FivePathState.HasExternalColorAt G s c s.right)
    {z : G.V}
    (p : (G.twoColorGraph (F.erase s.omitted) s.paint b c).Path
      s.right z)
    {i : ℕ} (hiLe : i ≤ p.1.length)
    (hfirst : ∀ j, 0 < j → j < i →
      p.1.getVert j ∉ s.path.1.support.toFinset)
    (hiZ2 : p.1.getVert i = s.path.1.getVert 2)
    {t : G.E} (htF : t ∈ F.erase s.omitted)
    (ht1 : G.Inc (s.path.1.getVert 1) t)
    (ht3 : G.Inc (s.path.1.getVert 3) t)
    (htC : s.paint t = c) :
    ∃ switched : G.E → Fin k,
      G.IsProperOn (F.erase s.omitted) switched ∧
      b ∈ G.missingColorsAt (F.erase s.omitted) switched s.left ∧
      a ∈ G.missingColorsAt (F.erase s.omitted) switched s.right ∧
      (∀ v ∈ s.path.1.support,
        ∀ r ∈ F.erase s.omitted, G.Inc v r →
          s.paint r = a → switched r = b) ∧
      (∀ v ∈ s.path.1.support,
        ∀ r ∈ F.erase s.omitted, G.Inc v r →
          s.paint r = b → switched r = a) ∧
      (∀ r, s.paint r ≠ a → s.paint r ≠ b →
        switched r = s.paint r) ∧
      ∃ q₂ : (G.twoColorGraph (F.erase s.omitted) switched b c).Path
          s.right (s.path.1.getVert 3),
        2 ≤ q₂.1.length ∧
        (G.twoColorGraph (F.erase s.omitted) switched b c).Adj
          (s.path.1.getVert 3) s.right ∧
        s.left ∉ q₂.1.support ∧
      ∃ circuit : (G.twoColorGraph (F.erase s.omitted) switched b c).Walk
          s.right s.right,
        circuit.IsCycle ∧
        s.left ∉ circuit.support ∧
        s.right ∈ circuit.support ∧
        s.path.1.getVert 1 ∈ circuit.support ∧
        s.path.1.getVert 2 ∈ circuit.support ∧
        s.path.1.getVert 3 ∈ circuit.support := by
  classical
  obtain ⟨switched, hproper, hswapA, hswapB, hother,
    q, hqLen, hqCap⟩ :=
    FivePathState.exists_switched_z2_prefix
      G s hcritical hleft hright p hiLe hfirst hiZ2
  have hmissing := FivePathState.ab_path_switch_missing_endpoints
    G s hswapA hswapB hother
  obtain ⟨g₁, _, g₃, hg₁F, hg₁1, hg₁2, hg₁A,
    _, _, _, _, hg₃F, hg₃3, hg₃R, hg₃A⟩ :=
    FivePathState.exists_three_surviving_path_edges G s
  let H := G.twoColorGraph (F.erase s.omitted) switched b c
  have hZ1mem : s.path.1.getVert 1 ∈ s.path.1.support :=
    s.path.1.getVert_mem_support 1
  have hZ3mem : s.path.1.getVert 3 ∈ s.path.1.support :=
    s.path.1.getVert_mem_support 3
  have hg₁B : switched g₁ = b :=
    hswapA _ hZ1mem g₁ hg₁F hg₁1 hg₁A
  have hg₃B : switched g₃ = b :=
    hswapA _ hZ3mem g₃ hg₃F hg₃3 hg₃A
  have hcne := FivePathState.external_endpoint_color_ne_missing
    G s hleft hright
  have htSw : switched t = c :=
    (hother t (by simpa [htC] using hcne.1)
      (by simpa [htC] using hcne.2)).trans htC
  have hZ21 : H.Adj (s.path.1.getVert 2) (s.path.1.getVert 1) := by
    have hne := (s.path.1.adj_getVert_succ
      (i := 1) (by have := s.path_len; omega)).ne
    exact G.twoColorGraph_adj_of_witness_inc hne.symm hg₁F hg₁2 hg₁1
      (Or.inl hg₁B)
  have hZ13 : H.Adj (s.path.1.getVert 1) (s.path.1.getVert 3) := by
    have hne : s.path.1.getVert 1 ≠ s.path.1.getVert 3 := by
      intro h
      have hidx := s.path.property.getVert_injOn
        (Set.mem_Iic.mpr (by have := s.path_len; omega : 1 ≤ s.path.1.length))
        (Set.mem_Iic.mpr (by have := s.path_len; omega : 3 ≤ s.path.1.length)) h
      omega
    exact G.twoColorGraph_adj_of_witness_inc hne htF ht1 ht3
      (Or.inr htSw)
  have hZ3Y : H.Adj (s.path.1.getVert 3) s.right := by
    have hne : s.path.1.getVert 3 ≠ s.right :=
      (FivePathState.internal_vertex_ne_endpoints G s
        (by omega : 0 < 3) (by omega : 3 < 4)).2
    exact G.twoColorGraph_adj_of_witness_inc hne hg₃F hg₃3 hg₃R
      (Or.inl hg₃B)
  have hZ1notQ : s.path.1.getVert 1 ∉ q.1.support := by
    intro hmem
    have hS : s.path.1.getVert 1 ∈ s.path.1.support.toFinset := by
      simpa only [List.mem_toFinset] using hZ1mem
    rcases hqCap _ hmem hS with hY | hZ2
    · exact (FivePathState.internal_vertex_ne_endpoints G s
        (by omega : 0 < 1) (by omega : 1 < 4)).2 hY
    · have hne := (s.path.1.adj_getVert_succ
        (i := 1) (by have := s.path_len; omega)).ne
      exact hne hZ2
  have hZ3notQ : s.path.1.getVert 3 ∉ q.1.support := by
    intro hmem
    have hS : s.path.1.getVert 3 ∈ s.path.1.support.toFinset := by
      simpa only [List.mem_toFinset] using hZ3mem
    rcases hqCap _ hmem hS with hY | hZ2
    · exact (FivePathState.internal_vertex_ne_endpoints G s
        (by omega : 0 < 3) (by omega : 3 < 4)).2 hY
    · have hne := (s.path.1.adj_getVert_succ
        (i := 2) (by have := s.path_len; omega)).ne
      exact hne.symm hZ2
  let q₁ : H.Path s.right (s.path.1.getVert 1) :=
    ⟨q.1.concat hZ21, q.property.concat hZ1notQ hZ21⟩
  have hZ3notQ₁ : s.path.1.getVert 3 ∉ q₁.1.support := by
    have hne : s.path.1.getVert 3 ≠ s.path.1.getVert 1 :=
      hZ13.ne.symm
    simpa [q₁, SimpleGraph.Walk.support_concat, hne] using hZ3notQ
  let q₂ : H.Path s.right (s.path.1.getVert 3) :=
    ⟨q₁.1.concat hZ13, q₁.property.concat hZ3notQ₁ hZ13⟩
  have hYneZ1 : s.right ≠ s.path.1.getVert 1 :=
    (FivePathState.internal_vertex_ne_endpoints G s
      (by omega : 0 < 1) (by omega : 1 < 4)).2.symm
  have hnoClose : s(s.right, s.path.1.getVert 3) ∉ q₂.1.edges := by
    intro hmem
    have hYpen := q₂.property.eq_penultimate_of_mem_edges
      (by simpa [Sym2.eq_swap] using hmem :
        s(s.path.1.getVert 3, s.right) ∈ q₂.1.edges)
    have hpen : q₂.1.penultimate = s.path.1.getVert 1 := by
      simp [q₂, SimpleGraph.Walk.penultimate_concat]
    exact hYneZ1 (hYpen.trans hpen)
  let qR : H.Path (s.path.1.getVert 3) s.right := q₂.reverse
  have hnoCloseR : s(s.right, s.path.1.getVert 3) ∉ qR.1.edges := by
    intro hmem
    apply hnoClose
    simpa [qR, SimpleGraph.Walk.edges_reverse] using hmem
  let circuit : H.Walk s.right s.right := .cons hZ3Y.symm qR.1
  have hcycle : circuit.IsCycle :=
    qR.cons_isCycle hZ3Y.symm hnoCloseR
  have hXnotQ : s.left ∉ q.1.support := by
    intro hmem
    have hS : s.left ∈ s.path.1.support.toFinset := by
      simpa only [List.mem_toFinset] using s.path.1.start_mem_support
    rcases hqCap _ hmem hS with hY | hZ2
    · exact s.left_ne_right hY
    · exact (FivePathState.internal_vertex_ne_endpoints G s
        (by omega : 0 < 2) (by omega : 2 < 4)).1 hZ2.symm
  have hXnotQ₂ : s.left ∉ q₂.1.support := by
    have hXneZ1 := (FivePathState.internal_vertex_ne_endpoints G s
      (by omega : 0 < 1) (by omega : 1 < 4)).1.symm
    have hXneZ3 := (FivePathState.internal_vertex_ne_endpoints G s
      (by omega : 0 < 3) (by omega : 3 < 4)).1.symm
    simpa [q₂, q₁, SimpleGraph.Walk.support_concat, hXneZ1, hXneZ3]
      using hXnotQ
  have hq₂Len : 2 ≤ q₂.1.length := by
    have hlen : q₂.1.length = q.1.length + 2 := by
      simp [q₂, q₁, SimpleGraph.Walk.length_concat]
    omega
  have hXnotCircuit : s.left ∉ circuit.support := by
    simpa [circuit, qR, SimpleGraph.Walk.support_cons,
      SimpleGraph.Walk.support_reverse, s.left_ne_right]
      using hXnotQ₂
  have hYmem : s.right ∈ circuit.support := circuit.start_mem_support
  have hZ2mem : s.path.1.getVert 2 ∈ circuit.support := by
    have hq := q.1.end_mem_support
    simp [circuit, qR, q₂, q₁, SimpleGraph.Walk.support_cons,
      SimpleGraph.Walk.support_reverse,
      SimpleGraph.Walk.support_concat] at *
  have hZ1memC : s.path.1.getVert 1 ∈ circuit.support := by
    simp [circuit, qR, q₂, q₁, SimpleGraph.Walk.support_cons,
      SimpleGraph.Walk.support_reverse,
      SimpleGraph.Walk.support_concat]
  have hZ3memC : s.path.1.getVert 3 ∈ circuit.support := by
    simp [circuit, qR, q₂, q₁, SimpleGraph.Walk.support_cons,
      SimpleGraph.Walk.support_reverse,
      SimpleGraph.Walk.support_concat]
  exact ⟨switched, hproper, hmissing.1, hmissing.2,
    hswapA, hswapB, hother, q₂, hq₂Len, hZ3Y,
    hXnotQ₂, circuit,
    hcycle, hXnotCircuit, hYmem, hZ1memC,
    hZ2mem, hZ3memC⟩

end WeightedEdgeColoring.WeightedMultigraph
