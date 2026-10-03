import WeightedEdgeColoring.SubtwoOrdinaryFivePresentForcedOutsideEdge

/-!
# The exterior edge forced by the V=Z1 middle-c circuit
-/

namespace WeightedEdgeColoring.WeightedMultigraph

universe u
variable (G : WeightedMultigraph.{u})

theorem FivePathState.exists_vz1_internal_c_forced_outside_a_edge
    {F : Finset G.E} {k d : ℕ} {a b c : Fin k}
    (s : G.FivePathState F k a b)
    (hcritical : G.IsColorCriticalOn F k)
    (hdk : d + 1 < k) (hdegree : ∀ z, G.degreeOn F z ≤ d)
    (hthreshold : 7 * d < 6 * k + 2)
    (hleft : FivePathState.HasExternalColorAt G s c s.left)
    (hright : FivePathState.HasExternalColorAt G s c s.right)
    (hZ1external : FivePathState.HasExternalColorAt G s c
      (s.path.1.getVert 1))
    (p : (G.twoColorGraph (F.erase s.omitted) s.paint b c).Path
      s.right s.left)
    {i : ℕ} (hi : 1 < i) (hiLe : i ≤ p.1.length)
    (hfirst : ∀ j, 0 < j → j < i →
      p.1.getVert j ∉ s.path.1.support.toFinset)
    (hiZ1 : p.1.getVert i = s.path.1.getVert 1)
    {t : G.E} (htF : t ∈ F.erase s.omitted)
    (ht2 : G.Inc (s.path.1.getVert 2) t)
    (ht3 : G.Inc (s.path.1.getVert 3) t)
    (htC : s.paint t = c) :
    ∃ paint₂ : G.E → Fin k,
      G.IsProperOn (F.erase s.omitted) paint₂ ∧
      ∃ w u, w ∉ s.path.1.support.toFinset ∧
        u ∉ s.path.1.support.toFinset ∧ w ≠ u ∧
        ∃ g ∈ F.erase s.omitted,
          G.Inc w g ∧ G.Inc u g ∧ paint₂ g = a := by
  classical
  obtain ⟨switched, hproper, hswapA, hswapB, hother, q, hqLen, hqSupport⟩ :=
    FivePathState.exists_switched_z1_prefix
      G s hcritical hleft hright p hi hiLe hfirst hiZ1
  have hmissing := FivePathState.ab_path_switch_missing_endpoints
    G s hswapA hswapB hother
  obtain ⟨g₁, g₂, g₃, hg₁F, hg₁1, hg₁2, hg₁A,
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
  have htSw : switched t = c := by
    exact (hother t (by simpa [htC] using hcne.1)
      (by simpa [htC] using hcne.2)).trans htC
  have hZ12 : H.Adj (s.path.1.getVert 1) (s.path.1.getVert 2) := by
    have hne := (s.path.1.adj_getVert_succ
      (i := 1) (by have := s.path_len; omega)).ne
    exact G.twoColorGraph_adj_of_witness_inc hne hg₁F hg₁1 hg₁2
      (Or.inl hg₁B)
  have hZ23 : H.Adj (s.path.1.getVert 2) (s.path.1.getVert 3) := by
    have hne := (s.path.1.adj_getVert_succ
      (i := 2) (by have := s.path_len; omega)).ne
    exact G.twoColorGraph_adj_of_witness_inc hne htF ht2 ht3
      (Or.inr htSw)
  have hZ3Y : H.Adj (s.path.1.getVert 3) s.right := by
    have hne : s.path.1.getVert 3 ≠ s.right :=
      (FivePathState.internal_vertex_ne_endpoints G s
        (by omega : 0 < 3) (by omega : 3 < 4)).2
    exact G.twoColorGraph_adj_of_witness_inc hne hg₃F hg₃3 hg₃R
      (Or.inl hg₃B)
  have hZ2notQ : s.path.1.getVert 2 ∉ q.1.support := by
    intro hmem
    have h2S : s.path.1.getVert 2 ∈ s.path.1.support.toFinset := by
      simpa only [List.mem_toFinset] using s.path.1.getVert_mem_support 2
    rcases hqSupport _ hmem h2S with hY | hZ1
    · exact (FivePathState.internal_vertex_ne_endpoints G s
        (by omega : 0 < 2) (by omega : 2 < 4)).2 hY
    · have hne := (s.path.1.adj_getVert_succ
        (i := 1) (by have := s.path_len; omega)).ne
      exact hne.symm hZ1
  have hZ3notQ : s.path.1.getVert 3 ∉ q.1.support := by
    intro hmem
    have h3S : s.path.1.getVert 3 ∈ s.path.1.support.toFinset := by
      simpa only [List.mem_toFinset] using s.path.1.getVert_mem_support 3
    rcases hqSupport _ hmem h3S with hY | hZ1
    · exact (FivePathState.internal_vertex_ne_endpoints G s
        (by omega : 0 < 3) (by omega : 3 < 4)).2 hY
    · have hidx := s.path.property.getVert_injOn
        (Set.mem_Iic.mpr (by have := s.path_len; omega : 3 ≤ s.path.1.length))
        (Set.mem_Iic.mpr (by have := s.path_len; omega : 1 ≤ s.path.1.length))
        hZ1
      omega
  let q₁ : H.Path s.right (s.path.1.getVert 2) :=
    ⟨q.1.concat hZ12, q.property.concat hZ2notQ hZ12⟩
  have hZ23ne : s.path.1.getVert 2 ≠ s.path.1.getVert 3 :=
    (s.path.1.adj_getVert_succ
      (i := 2) (by have := s.path_len; omega)).ne
  have hZ3notQ₁ : s.path.1.getVert 3 ∉ q₁.1.support := by
    simpa [q₁, SimpleGraph.Walk.support_concat, hZ23ne.symm]
      using hZ3notQ
  let q₂ : H.Path s.right (s.path.1.getVert 3) :=
    ⟨q₁.1.concat hZ23, q₁.property.concat hZ3notQ₁ hZ23⟩
  have hYneZ2 : s.right ≠ s.path.1.getVert 2 :=
    (FivePathState.internal_vertex_ne_endpoints G s
      (by omega : 0 < 2) (by omega : 2 < 4)).2.symm
  have hnoClose : s(s.right, s.path.1.getVert 3) ∉ q₂.1.edges := by
    intro hmem
    have hYpen := q₂.property.eq_penultimate_of_mem_edges
      (by simpa [Sym2.eq_swap] using hmem :
        s(s.path.1.getVert 3, s.right) ∈ q₂.1.edges)
    have hpen : q₂.1.penultimate = s.path.1.getVert 2 := by
      simp [q₂, SimpleGraph.Walk.penultimate_concat]
    exact hYneZ2 (hYpen.trans hpen)
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
    have hLS : s.left ∈ s.path.1.support.toFinset := by
      simpa only [List.mem_toFinset] using s.path.1.start_mem_support
    rcases hqSupport _ hmem hLS with hY | hZ1
    · exact s.left_ne_right hY
    · exact (FivePathState.internal_vertex_ne_endpoints G s
        (by omega : 0 < 1) (by omega : 1 < 4)).1 hZ1.symm
  have hXnotQ₂ : s.left ∉ q₂.1.support := by
    have hXneZ2 := (FivePathState.internal_vertex_ne_endpoints G s
      (by omega : 0 < 2) (by omega : 2 < 4)).1.symm
    have hXneZ3 := (FivePathState.internal_vertex_ne_endpoints G s
      (by omega : 0 < 3) (by omega : 3 < 4)).1.symm
    simpa [q₂, q₁, SimpleGraph.Walk.support_concat, hXneZ2, hXneZ3]
      using hXnotQ
  have hq₂Len : 2 ≤ q₂.1.length := by
    have hlen : q₂.1.length = q.1.length + 2 := by
      simp [q₂, q₁, SimpleGraph.Walk.length_concat]
    omega
  have hXnotCircuit : s.left ∉ circuit.support := by
    intro h
    simp only [circuit, SimpleGraph.Walk.support_cons,
      List.mem_cons] at h
    rcases h with hEq | hMem
    · exact s.left_ne_right hEq
    · exact hXnotQ₂ (by simpa [qR] using hMem)
  obtain ⟨paint₂, hproper₂, hcX, haY₂, hother₂, hstable₂,
    qCA, hqCard⟩ :=
    FivePathState.exists_second_switch_outside_right_circuit
      G s hcritical hdk hdegree hthreshold
      hproper hmissing.1 hmissing.2 q₂ hq₂Len hZ3Y hXnotQ₂
  have hZ1memQ₂ : s.path.1.getVert 1 ∈ q₂.1.support := by
    have hqEnd := q.1.end_mem_support
    simp [q₂, q₁, SimpleGraph.Walk.support_concat] at *
  have hYmemQ₂ : s.right ∈ q₂.1.support := q₂.1.start_mem_support
  have hZ1S : s.path.1.getVert 1 ∈ s.path.1.support.toFinset := by
    simpa only [List.mem_toFinset] using hZ1mem
  have hYS : s.right ∈ s.path.1.support.toFinset := by
    simpa only [List.mem_toFinset] using s.path.1.end_mem_support
  have hZ1Y : s.path.1.getVert 1 ≠ s.right :=
    (FivePathState.internal_vertex_ne_endpoints G s
      (by omega : 0 < 1) (by omega : 1 < 4)).2
  obtain ⟨u, w, huw, huOut, hwOut, gU, gW,
    hgUF, hgWF, hgUY, hgUU, hgWZ, hgWW, hgUC, hgWC⟩ :=
    FivePathState.distinct_outside_neighbors_of_external_pair
      G s hYS hZ1S hZ1Y.symm hright hZ1external
  have hgUSw : switched gU = c :=
    (hother gU (by simpa [hgUC] using hcne.1)
      (by simpa [hgUC] using hcne.2)).trans hgUC
  have hgWSw : switched gW = c :=
    (hother gW (by simpa [hgWC] using hcne.1)
      (by simpa [hgWC] using hcne.2)).trans hgWC
  have hgU₂ : paint₂ gU = c :=
    (hstable₂ s.right hYmemQ₂ gU hgUF hgUY).trans hgUSw
  have hgW₂ : paint₂ gW = c :=
    (hstable₂ (s.path.1.getVert 1) hZ1memQ₂ gW hgWF hgWZ).trans hgWSw
  obtain ⟨g₀, hg₀F, hg₀X, hg₀Z, hg₀B⟩ :=
    FivePathState.exists_first_b_edge G s
  have hg₀Sw : switched g₀ = a :=
    hswapB s.left s.path.1.start_mem_support g₀ hg₀F hg₀X hg₀B
  have hab : a ≠ b := by
    intro h
    exact (G.color_ne_of_mem_missingColorsAt
      (F.erase s.omitted) s.paint s.left a s.left_missing
      hg₀F hg₀X) (hg₀B.trans h.symm)
  have hg₀₂ : paint₂ g₀ = a :=
    (hother₂ g₀ (by simpa [hg₀Sw] using hab)
      (by simpa [hg₀Sw] using hcne.1.symm)).trans hg₀Sw
  obtain ⟨g, hgF, hgw, hgu, hgA⟩ :=
    G.forced_outside_a_edge_of_five_critical_path
      hcritical s.omitted_mem hproper₂ s.left_ne_right
      (FivePathState.internal_vertex_ne_endpoints G s
        (by omega : 0 < 1) (by omega : 1 < 4)).1.symm
      hZ1Y
      s.left_inc s.right_inc hcX haY₂
      (by simpa only [List.mem_toFinset] using s.path.1.start_mem_support)
      hZ1S hYS hwOut huOut huw.symm
      hg₀F hg₀X hg₀Z hg₀₂
      hgWF hgWZ hgWW hgW₂
      hgUF hgUY hgUU hgU₂ qCA hqCard
  exact ⟨paint₂, hproper₂, w, u, hwOut, huOut, huw.symm,
    g, hgF, hgw, hgu, hgA⟩


end WeightedEdgeColoring.WeightedMultigraph
