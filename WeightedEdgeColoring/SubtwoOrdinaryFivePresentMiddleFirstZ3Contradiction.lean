import WeightedEdgeColoring.SubtwoOrdinaryFivePresentMiddleFirstZ3Prefix

/-!
# A first return at Z₃ closes immediately after the critical-chain switch
-/

namespace WeightedEdgeColoring.WeightedMultigraph

universe u
variable (G : WeightedMultigraph.{u})

theorem FivePathState.false_of_middle_first_z3
    {F : Finset G.E} {k D : ℕ} {a b c : Fin k}
    (s : G.FivePathState F k a b)
    (hcritical : G.IsColorCriticalOn F k)
    (hdk : D + 1 < k) (hdegree : ∀ z, G.degreeOn F z ≤ D)
    (hthreshold : 7 * D < 6 * k + 2)
    (hleft : FivePathState.HasExternalColorAt G s c s.left)
    (hright : FivePathState.HasExternalColorAt G s c s.right)
    (hZ3 : FivePathState.HasExternalColorAt G s c
      (s.path.1.getVert 3))
    {z : G.V}
    (p : (G.twoColorGraph (F.erase s.omitted) s.paint b c).Path
      s.right z)
    {i : ℕ} (hi : 1 < i) (hiLe : i ≤ p.1.length)
    (hfirst : ∀ j, 0 < j → j < i →
      p.1.getVert j ∉ s.path.1.support.toFinset)
    (hiZ3 : p.1.getVert i = s.path.1.getVert 3) : False := by
  classical
  obtain ⟨paint₁,hproper₁,hswapA,hswapB,hother,
    q,hqLen,hqCap⟩ :=
    FivePathState.exists_switched_z3_prefix
      G s hcritical hleft hright p hiLe hfirst hiZ3
  have hmissing := FivePathState.ab_path_switch_missing_endpoints
    G s hswapA hswapB hother
  obtain ⟨g₁,g₂,g₃,hg₁F,hg₁1,hg₁2,hg₁A,
    hg₂F,hg₂2,hg₂3,hg₂B,hg₃F,hg₃3,hg₃Y,hg₃A⟩ :=
    FivePathState.exists_three_surviving_path_edges G s
  have hS1 : s.path.1.getVert 1 ∈ s.path.1.support :=
    s.path.1.getVert_mem_support 1
  have hS2 : s.path.1.getVert 2 ∈ s.path.1.support :=
    s.path.1.getVert_mem_support 2
  have hS3 : s.path.1.getVert 3 ∈ s.path.1.support :=
    s.path.1.getVert_mem_support 3
  have hg₁One : paint₁ g₁ = b :=
    hswapA _ hS1 g₁ hg₁F hg₁1 hg₁A
  have hg₂One : paint₁ g₂ = a :=
    hswapB _ hS2 g₂ hg₂F hg₂2 hg₂B
  have hg₃One : paint₁ g₃ = b :=
    hswapA _ hS3 g₃ hg₃F hg₃3 hg₃A
  let H := G.twoColorGraph (F.erase s.omitted) paint₁ b c
  have hclose : H.Adj (s.path.1.getVert 3) s.right :=
    G.twoColorGraph_adj_of_witness_inc
      (FivePathState.internal_vertex_ne_endpoints G s
        (by omega : 0 < 3) (by omega : 3 < 4)).2
      hg₃F hg₃3 hg₃Y (Or.inl hg₃One)
  have hmax : ∀ v, H.degree v ≤ 2 := by
    intro v
    exact G.twoColorGraph_degree_le_two_of_isProperOn
      (F.erase s.omitted) paint₁ hproper₁ b c v
  have h2Len : 2 ≤ q.1.length := by omega
  have hOut {v : G.V}
      (hvS : v ∈ s.path.1.support.toFinset)
      (hvY : v ≠ s.right)
      (hv3 : v ≠ s.path.1.getVert 3) : v ∉ q.1.support := by
    intro hv
    rcases hqCap v hv hvS with hY | h3
    · exact hvY hY
    · exact hv3 h3
  have hXout : s.left ∉ q.1.support :=
    hOut (by simpa only [List.mem_toFinset] using
      s.path.1.start_mem_support) s.left_ne_right
      (FivePathState.internal_vertex_ne_endpoints G s
        (by omega : 0 < 3) (by omega : 3 < 4)).1.symm
  have h1out : s.path.1.getVert 1 ∉ q.1.support :=
    hOut (by simpa only [List.mem_toFinset] using hS1)
      (FivePathState.internal_vertex_ne_endpoints G s
        (by omega : 0 < 1) (by omega : 1 < 4)).2
      (by
        intro h
        have hidx := s.path.property.getVert_injOn
          (Set.mem_Iic.mpr (by have := s.path_len; omega : 1 ≤ s.path.1.length))
          (Set.mem_Iic.mpr (by have := s.path_len; omega : 3 ≤ s.path.1.length)) h
        omega)
  have h2out : s.path.1.getVert 2 ∉ q.1.support :=
    hOut (by simpa only [List.mem_toFinset] using hS2)
      (FivePathState.internal_vertex_ne_endpoints G s
        (by omega : 0 < 2) (by omega : 2 < 4)).2
      (s.path.1.adj_getVert_succ
        (i := 2) (by have := s.path_len; omega)).ne
  have hsep {v : G.V} (hvOut : v ∉ q.1.support) :
      H.connectedComponentMk v ≠ H.connectedComponentMk s.right := by
    intro heq
    have hmem := G.mem_closedPath_support_of_same_component
      H q h2Len hclose.symm hmax heq
    exact hvOut hmem
  let flip : H.ConnectedComponent → Prop :=
    fun C ↦ C = H.connectedComponentMk s.right
  letI : DecidablePred flip := Classical.decPred _
  let paint₂ := G.kempeComponentSwitch
    (F.erase s.omitted) paint₁ b c flip
  have hproper₂ : G.IsProperOn (F.erase s.omitted) paint₂ :=
    G.isProperOn_kempeComponentSwitch
      (F.erase s.omitted) paint₁ hproper₁ b c flip
  have hbX₂ : b ∈ G.missingColorsAt
      (F.erase s.omitted) paint₂ s.left :=
    (G.mem_missingColorsAt_kempeComponentSwitch_of_not_flip_iff
      (F.erase s.omitted) paint₁ b c flip s.left (hsep hXout) b).mpr
      hmissing.1
  have hcne := FivePathState.external_endpoint_color_ne_missing
    G s hleft hright
  obtain ⟨g₀,hg₀F,hg₀X,hg₀1,hg₀B⟩ :=
    FivePathState.exists_first_b_edge G s
  have hab : a ≠ b := by
    intro h
    exact (G.color_ne_of_mem_missingColorsAt
      (F.erase s.omitted) s.paint s.left a s.left_missing
      hg₀F hg₀X) (hg₀B.trans h.symm)
  have haY₂ : a ∈ G.missingColorsAt
      (F.erase s.omitted) paint₂ s.right :=
    (G.mem_missingColorsAt_kempeComponentSwitch_of_fixedColor_iff
      (F := F.erase s.omitted) paint₁ b c flip s.right a
      hab hcne.1.symm).mpr hmissing.2
  have hg₀One : paint₁ g₀ = a :=
    hswapB s.left s.path.1.start_mem_support g₀ hg₀F hg₀X hg₀B
  have hg₀Two : paint₂ g₀ = a :=
    (G.kempeComponentSwitch_eq_of_color_ne paint₁ b c flip g₀
      (by simpa [hg₀One] using hab)
      (by simpa [hg₀One] using hcne.1.symm)).trans hg₀One
  have hg₁Two : paint₂ g₁ = b := by
    change G.kempeComponentSwitch (F.erase s.omitted)
      paint₁ b c flip g₁ = b
    rw [G.kempeComponentSwitch_eq_localPerm
      (F.erase s.omitted) paint₁ b c flip hg₁F hg₁1]
    simp [kempeLocalPerm, flip, H, hsep h1out, hg₁One]
  have hg₂Two : paint₂ g₂ = a :=
    (G.kempeComponentSwitch_eq_of_color_ne paint₁ b c flip g₂
      (by simpa [hg₂One] using hab)
      (by simpa [hg₂One] using hcne.1.symm)).trans hg₂One
  obtain ⟨r,hrF,hr3,hrC,hrExt⟩ := hZ3
  have h3Sf : s.path.1.getVert 3 ∈ s.path.1.support.toFinset := by
    simpa only [List.mem_toFinset] using hS3
  obtain ⟨w,hrw,hwOut,_⟩ :=
    FivePathState.outside_neighbor_of_external_edge
      G s h3Sf hrF hrExt
  have hrOne : paint₁ r = c :=
    (hother r (by simpa [hrC] using hcne.1)
      (by simpa [hrC] using hcne.2)).trans hrC
  have hZ3comp : H.connectedComponentMk
      (s.path.1.getVert 3) = H.connectedComponentMk s.right :=
    (SimpleGraph.ConnectedComponent.sound ⟨q.1⟩).symm
  have hrTwo : paint₂ r = b := by
    change G.kempeComponentSwitch (F.erase s.omitted)
      paint₁ b c flip r = b
    rw [G.kempeComponentSwitch_eq_localPerm
      (F.erase s.omitted) paint₁ b c flip hrF hr3]
    simp [kempeLocalPerm, flip, H, hZ3comp, hrOne]
  let K := G.twoColorGraph (F.erase s.omitted) paint₂ b a
  have hX1 : K.Adj s.left (s.path.1.getVert 1) :=
    G.twoColorGraph_adj_of_witness_inc
      (FivePathState.internal_vertex_ne_endpoints G s
        (by omega : 0 < 1) (by omega : 1 < 4)).1.symm
      hg₀F hg₀X hg₀1 (Or.inr hg₀Two)
  have h12 : K.Adj (s.path.1.getVert 1)
      (s.path.1.getVert 2) :=
    G.twoColorGraph_adj_of_witness_inc
      (s.path.1.adj_getVert_succ
        (i := 1) (by have := s.path_len; omega)).ne
      hg₁F hg₁1 hg₁2 (Or.inl hg₁Two)
  have h23 : K.Adj (s.path.1.getVert 2)
      (s.path.1.getVert 3) :=
    G.twoColorGraph_adj_of_witness_inc
      (s.path.1.adj_getVert_succ
        (i := 2) (by have := s.path_len; omega)).ne
      hg₂F hg₂2 hg₂3 (Or.inr hg₂Two)
  have h3W : K.Adj (s.path.1.getVert 3) w :=
    G.twoColorGraph_adj_of_witness_inc
      (by intro h; exact hwOut (h ▸ h3Sf))
      hrF hr3 hrw (Or.inl hrTwo)
  have hXY := G.critical_endpoints_same_twoColorComponent_at
    hcritical s.omitted_mem hproper₂ s.left_ne_right
    s.left_inc s.right_inc hbX₂ haY₂
  have hreach : K.Reachable s.left s.right :=
    SimpleGraph.ConnectedComponent.exact hXY
  obtain ⟨walk⟩ := hreach
  let qCrit := walk.toPath
  have h1comp : K.connectedComponentMk (s.path.1.getVert 1) =
      K.connectedComponentMk s.left :=
    (SimpleGraph.ConnectedComponent.connectedComponentMk_eq_of_adj hX1).symm
  have h2comp : K.connectedComponentMk (s.path.1.getVert 2) =
      K.connectedComponentMk s.left :=
    (SimpleGraph.ConnectedComponent.connectedComponentMk_eq_of_adj h12).symm.trans
      h1comp
  have h3comp : K.connectedComponentMk (s.path.1.getVert 3) =
      K.connectedComponentMk s.left :=
    (SimpleGraph.ConnectedComponent.connectedComponentMk_eq_of_adj h23).symm.trans
      h2comp
  have hwcomp : K.connectedComponentMk w =
      K.connectedComponentMk s.left :=
    (SimpleGraph.ConnectedComponent.connectedComponentMk_eq_of_adj h3W).symm.trans
      h3comp
  have hsupport : ∀ v ∈ s.path.1.support,
      K.connectedComponentMk v = K.connectedComponentMk s.left := by
    intro v hv
    have hverts := FivePathState.support_eq_five_vertices G s
    have hvF : v ∈ s.path.1.support.toFinset := by simpa using hv
    rw [hverts] at hvF
    simp only [Finset.mem_insert, Finset.mem_singleton] at hvF
    rcases hvF with hX | h1 | h2 | h3 | hY
    · simpa [hX]
    · simpa [h1] using h1comp
    · simpa [h2] using h2comp
    · simpa [h3] using h3comp
    · simpa [hY] using hXY.symm
  exact G.criticalPath_not_contains_fivePath_and_external_at
    s hcritical s.omitted_mem hproper₂ s.left_ne_right
    s.left_inc s.right_inc hbX₂ haY₂ qCrit
    hdk hdegree hthreshold hsupport hwOut hwcomp

end WeightedEdgeColoring.WeightedMultigraph
