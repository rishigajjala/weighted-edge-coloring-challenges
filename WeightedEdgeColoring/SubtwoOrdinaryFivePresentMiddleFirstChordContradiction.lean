import WeightedEdgeColoring.SubtwoOrdinaryFivePresentMiddleFirstChordCircuit
import WeightedEdgeColoring.SubtwoOrdinaryFivePresentCircuitContradiction

/-!
# Six vertices on the switched critical chain in the cross-chord case
-/

namespace WeightedEdgeColoring.WeightedMultigraph

universe u
variable (G : WeightedMultigraph.{u})

theorem FivePathState.false_of_middle_first_z2_cross_chord
    {F : Finset G.E} {k D : ℕ} {a b c : Fin k}
    (s : G.FivePathState F k a b)
    (hcritical : G.IsColorCriticalOn F k)
    (hdk : D + 1 < k) (hdegree : ∀ z, G.degreeOn F z ≤ D)
    (hthreshold : 7 * D < 6 * k + 2)
    (hleft : FivePathState.HasExternalColorAt G s c s.left)
    (hright : FivePathState.HasExternalColorAt G s c s.right)
    (hZ2 : FivePathState.HasExternalColorAt G s c
      (s.path.1.getVert 2))
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
    (htC : s.paint t = c) : False := by
  classical
  obtain ⟨paint₁, hproper₁, hbX, haY,
    hswapA, hswapB, hother,
    q₂, hqLen, hclose, hXout,
    circuit, _, _, _, hZ1C, hZ2C, hZ3C⟩ :=
    FivePathState.exists_middle_first_cross_chord_circuit
      G s hcritical hleft hright p hiLe hfirst hiZ2
      htF ht1 ht3 htC
  let H := G.twoColorGraph (F.erase s.omitted) paint₁ b c
  have hmax : ∀ v, H.degree v ≤ 2 := by
    intro v
    exact G.twoColorGraph_degree_le_two_of_isProperOn
      (F.erase s.omitted) paint₁ hproper₁ b c v
  have hsep : H.connectedComponentMk s.left ≠
      H.connectedComponentMk s.right := by
    intro h
    have hmem := G.mem_closedPath_support_of_same_component
      H q₂ hqLen hclose.symm hmax h
    exact hXout hmem
  let flip : H.ConnectedComponent → Prop :=
    fun C ↦ C = H.connectedComponentMk s.right
  letI : DecidablePred flip := Classical.decPred _
  let paint₂ := G.kempeComponentSwitch
    (F.erase s.omitted) paint₁ b c flip
  have hproper₂ : G.IsProperOn (F.erase s.omitted) paint₂ :=
    G.isProperOn_kempeComponentSwitch
      (F.erase s.omitted) paint₁ hproper₁ b c flip
  have hXnot : ¬flip (H.connectedComponentMk s.left) := hsep
  have hbX₂ : b ∈ G.missingColorsAt
      (F.erase s.omitted) paint₂ s.left :=
    (G.mem_missingColorsAt_kempeComponentSwitch_of_not_flip_iff
      (F.erase s.omitted) paint₁ b c flip s.left hXnot b).mpr hbX
  have hcne := FivePathState.external_endpoint_color_ne_missing
    G s hleft hright
  have haY₂ : a ∈ G.missingColorsAt
      (F.erase s.omitted) paint₂ s.right :=
    (G.mem_missingColorsAt_kempeComponentSwitch_of_fixedColor_iff
      (F := F.erase s.omitted) paint₁ b c flip s.right a
      (by
        intro h
        obtain ⟨g,hgF,hgL,_,hgB⟩ := FivePathState.exists_first_b_edge G s
        exact (G.color_ne_of_mem_missingColorsAt
          (F.erase s.omitted) s.paint s.left a s.left_missing
          hgF hgL) (hgB.trans h.symm))
      hcne.1.symm).mpr haY
  have hcompC {v : G.V} (hv : v ∈ circuit.support) :
      H.connectedComponentMk v = H.connectedComponentMk s.right := by
    have hreach : H.Reachable s.right v :=
      ⟨circuit.takeUntil v hv⟩
    exact (SimpleGraph.ConnectedComponent.sound hreach).symm
  have hflipZ1 : flip (H.connectedComponentMk
      (s.path.1.getVert 1)) := hcompC hZ1C
  have hflipZ2 : flip (H.connectedComponentMk
      (s.path.1.getVert 2)) := hcompC hZ2C
  have hflipZ3 : flip (H.connectedComponentMk
      (s.path.1.getVert 3)) := hcompC hZ3C
  obtain ⟨g₀,hg₀F,hg₀X,hg₀1,hg₀B⟩ :=
    FivePathState.exists_first_b_edge G s
  obtain ⟨g₁,g₂,g₃,hg₁F,hg₁1,hg₁2,hg₁A,
    hg₂F,hg₂2,hg₂3,hg₂B,hg₃F,hg₃3,hg₃Y,hg₃A⟩ :=
    FivePathState.exists_three_surviving_path_edges G s
  have hS0 : s.left ∈ s.path.1.support := s.path.1.start_mem_support
  have hS1 : s.path.1.getVert 1 ∈ s.path.1.support :=
    s.path.1.getVert_mem_support 1
  have hS2 : s.path.1.getVert 2 ∈ s.path.1.support :=
    s.path.1.getVert_mem_support 2
  have hS3 : s.path.1.getVert 3 ∈ s.path.1.support :=
    s.path.1.getVert_mem_support 3
  have hab : a ≠ b := by
    intro h
    exact (G.color_ne_of_mem_missingColorsAt
      (F.erase s.omitted) s.paint s.left a s.left_missing
      hg₀F hg₀X) (hg₀B.trans h.symm)
  have hg₀One : paint₁ g₀ = a :=
    hswapB s.left hS0 g₀ hg₀F hg₀X hg₀B
  have hg₂One : paint₁ g₂ = a :=
    hswapB _ hS2 g₂ hg₂F hg₂2 hg₂B
  have htOne : paint₁ t = c :=
    (hother t (by simpa [htC] using hcne.1)
      (by simpa [htC] using hcne.2)).trans htC
  obtain ⟨r,hrF,hr2,hrC,hrExt⟩ := hZ2
  have h2Sf : s.path.1.getVert 2 ∈ s.path.1.support.toFinset := by
    simpa only [List.mem_toFinset] using hS2
  obtain ⟨w,hrw,hwOut,_⟩ :=
    FivePathState.outside_neighbor_of_external_edge
      G s h2Sf hrF hrExt
  have hrOne : paint₁ r = c :=
    (hother r (by simpa [hrC] using hcne.1)
      (by simpa [hrC] using hcne.2)).trans hrC
  have hg₀Two : paint₂ g₀ = a :=
    (G.kempeComponentSwitch_eq_of_color_ne
      paint₁ b c flip g₀
      (by simpa [hg₀One] using hab)
      (by simpa [hg₀One] using hcne.1.symm)).trans hg₀One
  have hg₂Two : paint₂ g₂ = a :=
    (G.kempeComponentSwitch_eq_of_color_ne
      paint₁ b c flip g₂
      (by simpa [hg₂One] using hab)
      (by simpa [hg₂One] using hcne.1.symm)).trans hg₂One
  have htTwo : paint₂ t = b := by
    change G.kempeComponentSwitch (F.erase s.omitted)
      paint₁ b c flip t = b
    rw [G.kempeComponentSwitch_eq_localPerm
      (F.erase s.omitted) paint₁ b c flip htF ht1]
    simp [kempeLocalPerm, flip, H, hflipZ1, htOne]
  have hrTwo : paint₂ r = b := by
    change G.kempeComponentSwitch (F.erase s.omitted)
      paint₁ b c flip r = b
    rw [G.kempeComponentSwitch_eq_localPerm
      (F.erase s.omitted) paint₁ b c flip hrF hr2]
    simp [kempeLocalPerm, flip, H, hflipZ2, hrOne]
  let K := G.twoColorGraph (F.erase s.omitted) paint₂ b a
  have hX1 : K.Adj s.left (s.path.1.getVert 1) :=
    G.twoColorGraph_adj_of_witness_inc
      (FivePathState.internal_vertex_ne_endpoints G s
        (by omega : 0 < 1) (by omega : 1 < 4)).1.symm
      hg₀F hg₀X hg₀1 (Or.inr hg₀Two)
  have h13 : K.Adj (s.path.1.getVert 1)
      (s.path.1.getVert 3) :=
    G.twoColorGraph_adj_of_witness_inc
      (by
        intro h
        have hidx := s.path.property.getVert_injOn
          (Set.mem_Iic.mpr (by have := s.path_len; omega : 1 ≤ s.path.1.length))
          (Set.mem_Iic.mpr (by have := s.path_len; omega : 3 ≤ s.path.1.length)) h
        omega)
      htF ht1 ht3 (Or.inl htTwo)
  have h32 : K.Adj (s.path.1.getVert 3)
      (s.path.1.getVert 2) :=
    G.twoColorGraph_adj_of_witness_inc
      (s.path.1.adj_getVert_succ
        (i := 2) (by have := s.path_len; omega)).ne.symm
      hg₂F hg₂3 hg₂2 (Or.inr hg₂Two)
  have h2W : K.Adj (s.path.1.getVert 2) w :=
    G.twoColorGraph_adj_of_witness_inc
      (by intro h; exact hwOut (h ▸ h2Sf))
      hrF hr2 hrw (Or.inl hrTwo)
  have hXY := G.critical_endpoints_same_twoColorComponent_at
    hcritical s.omitted_mem hproper₂ s.left_ne_right
    s.left_inc s.right_inc hbX₂ haY₂
  have hreach : K.Reachable s.left s.right :=
    SimpleGraph.ConnectedComponent.exact hXY
  obtain ⟨walk⟩ := hreach
  let q := walk.toPath
  have h1comp : K.connectedComponentMk (s.path.1.getVert 1) =
      K.connectedComponentMk s.left :=
    (SimpleGraph.ConnectedComponent.connectedComponentMk_eq_of_adj hX1).symm
  have h3comp : K.connectedComponentMk (s.path.1.getVert 3) =
      K.connectedComponentMk s.left :=
    (SimpleGraph.ConnectedComponent.connectedComponentMk_eq_of_adj h13).symm.trans
      h1comp
  have h2comp : K.connectedComponentMk (s.path.1.getVert 2) =
      K.connectedComponentMk s.left :=
    (SimpleGraph.ConnectedComponent.connectedComponentMk_eq_of_adj h32).symm.trans
      h3comp
  have hwcomp : K.connectedComponentMk w =
      K.connectedComponentMk s.left :=
    (SimpleGraph.ConnectedComponent.connectedComponentMk_eq_of_adj h2W).symm.trans
      h2comp
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
    s.left_inc s.right_inc hbX₂ haY₂ q
    hdk hdegree hthreshold hsupport hwOut hwcomp

end WeightedEdgeColoring.WeightedMultigraph
