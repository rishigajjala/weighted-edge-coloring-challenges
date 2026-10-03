import WeightedEdgeColoring.SubtwoOrdinaryFivePresentCircuitSwitch

/-!
# The six-vertex contradiction for Andersen's switched circuit
-/

namespace WeightedEdgeColoring.WeightedMultigraph

universe u
variable (G : WeightedMultigraph.{u})

/-- A critical endpoint path cannot contain all five vertices of an
existing five-path and a sixth vertex outside it at the seven-sixths
threshold. -/
theorem criticalPath_not_contains_fivePath_and_external_at
    {F : Finset G.E} {k d : ℕ} {a b : Fin k}
    (s : G.FivePathState F k a b)
    (hcritical : G.IsColorCriticalOn F k)
    {e : G.E} (heF : e ∈ F) {paint : G.E → Fin k}
    (hproper : G.IsProperOn (F.erase e) paint)
    {x y : G.V} (hxy : x ≠ y) (hxe : G.Inc x e) (hye : G.Inc y e)
    {α β : Fin k}
    (hα : α ∈ G.missingColorsAt (F.erase e) paint x)
    (hβ : β ∈ G.missingColorsAt (F.erase e) paint y)
    (q : (G.twoColorGraph (F.erase e) paint α β).Path x y)
    (hdk : d + 1 < k) (hdegree : ∀ z, G.degreeOn F z ≤ d)
    (hthreshold : 7 * d < 6 * k + 2)
    (hcomp : ∀ v ∈ s.path.1.support,
      (G.twoColorGraph (F.erase e) paint α β).connectedComponentMk v =
        (G.twoColorGraph (F.erase e) paint α β).connectedComponentMk x)
    {w : G.V} (hwOut : w ∉ s.path.1.support.toFinset)
    (hwComp : (G.twoColorGraph (F.erase e) paint α β).connectedComponentMk w =
      (G.twoColorGraph (F.erase e) paint α β).connectedComponentMk x) :
    False := by
  classical
  have hpCard : s.path.1.support.toFinset.card = 5 := by
    rw [List.toFinset_card_of_nodup s.path.property.support_nodup,
      s.path.1.length_support, s.path_len]
  have hsub : insert w s.path.1.support.toFinset ⊆ q.1.support.toFinset := by
    intro v hv
    rcases Finset.mem_insert.mp hv with rfl | hv
    · simpa only [List.mem_toFinset] using
        G.mem_criticalPath_support_of_same_twoColorComponent_at
          hcritical heF hproper hxy hxe hye hα hβ q hwComp
    · simpa only [List.mem_toFinset] using
        G.mem_criticalPath_support_of_same_twoColorComponent_at
          hcritical heF hproper hxy hxe hye hα hβ q
          (hcomp v (by simpa only [List.mem_toFinset] using hv))
  have hsmall := G.criticalPath_support_card_le_five_at
    hcritical heF hproper hxy hxe hye hα hβ q
    hdk hdegree hthreshold
  have hcard : (insert w s.path.1.support.toFinset).card = 6 := by
    simp [hwOut, hpCard]
  have hlarge := Finset.card_le_card hsub
  omega

/-- The middle vertex of a simple five-path is not incident with its
first edge, regardless of the orientation of that edge. -/
theorem FivePathState.middle_not_incident_first_edge
    {F : Finset G.E} {k : ℕ} {a b : Fin k}
    (s : G.FivePathState F k a b)
    {g : G.E} (hgL : G.Inc s.left g)
    (hg1 : G.Inc (s.path.1.getVert 1) g) :
    ¬G.Inc (s.path.1.getVert 2) g := by
  have hlen := s.path_len
  have hne01 : s.left ≠ s.path.1.getVert 1 := by
    intro h
    have hidx := s.path.property.getVert_injOn
      (Set.mem_Iic.mpr (by omega : 0 ≤ s.path.1.length))
      (Set.mem_Iic.mpr (by omega : 1 ≤ s.path.1.length))
      (by simpa using h)
    omega
  have hne02 : s.path.1.getVert 2 ≠ s.left := by
    intro h
    have hidx := s.path.property.getVert_injOn
      (Set.mem_Iic.mpr (by omega : 2 ≤ s.path.1.length))
      (Set.mem_Iic.mpr (by omega : 0 ≤ s.path.1.length))
      (by simpa using h)
    omega
  have hne12 : s.path.1.getVert 2 ≠ s.path.1.getVert 1 := by
    intro h
    have hidx := s.path.property.getVert_injOn
      (Set.mem_Iic.mpr (by omega : 2 ≤ s.path.1.length))
      (Set.mem_Iic.mpr (by omega : 1 ≤ s.path.1.length)) h
    omega
  have hends := G.endpoint_eq_or_endpoint_eq_swap_of_inc hne01 hgL hg1
  intro hinc
  rcases hends with ⟨hfst, hsnd⟩ | ⟨hfst, hsnd⟩
  · rcases hinc with h | h
    · exact hne02 (h.symm.trans hfst)
    · exact hne12 (h.symm.trans hsnd)
  · rcases hinc with h | h
    · exact hne12 (h.symm.trans hfst)
    · exact hne02 (h.symm.trans hsnd)

/-- In the ordered `V = X` branch, where neither `Z₁` nor `Z₂` occurs
before the first return to the old five-path, switching the closed
`(b,c)` circuit creates a six-vertex critical `(b,a)` component. -/
theorem FivePathState.first_hit_left_circuit_impossible
    {F : Finset G.E} {k d : ℕ} {a b c : Fin k}
    (s : G.FivePathState F k a b)
    (hcritical : G.IsColorCriticalOn F k)
    (hdk : d + 1 < k) (hdegree : ∀ z, G.degreeOn F z ≤ d)
    (hthreshold : 7 * d < 6 * k + 2)
    (hleft : FivePathState.HasExternalColorAt G s c s.left)
    (hright : FivePathState.HasExternalColorAt G s c s.right)
    (p : (G.twoColorGraph (F.erase s.omitted) s.paint b c).Path
      s.right s.left)
    (hZ1out : s.path.1.getVert 1 ∉ p.1.support)
    (hZ2out : s.path.1.getVert 2 ∉ p.1.support) : False := by
  classical
  obtain ⟨g, hgF, hgL, hg1, hgB, switched, hproper,
    hb, ha, hother, hstable, hrightSwap⟩ :=
    FivePathState.exists_first_hit_left_circuit_switch_palettes
      G s hleft hright p hZ1out
  obtain ⟨g₁, g₂, g₃, hg₁F, hg₁1, hg₁2, hg₁A,
    hg₂F, hg₂2, hg₂3, hg₂B,
    hg₃F, hg₃3, hg₃R, hg₃A⟩ :=
    FivePathState.exists_three_surviving_path_edges G s
  have hrightCopy := hright
  obtain ⟨r, hrF, hrR, hrC, hrExt⟩ := hrightCopy
  have hRmem : s.right ∈ s.path.1.support.toFinset := by
    simpa only [List.mem_toFinset] using s.path.1.end_mem_support
  obtain ⟨w, hrw, hwOut, hwNeR⟩ :=
    FivePathState.outside_neighbor_of_external_edge G s hRmem hrF hrExt
  have hab : a ≠ b := by
    intro h
    have hne := G.color_ne_of_mem_missingColorsAt
      (F.erase s.omitted) s.paint s.left a s.left_missing hgF hgL
    exact hne (hgB.trans h.symm)
  have hac : a ≠ c :=
    Ne.symm (FivePathState.external_endpoint_color_ne_missing
      G s hleft hright).1
  have hcb : c ≠ b :=
    (FivePathState.external_endpoint_color_ne_missing
      G s hleft hright).2
  let shifted := G.assignEdgeColor s.paint s.omitted b
  have h₁ne : g₁ ≠ g := by
    intro h
    exact hab (hg₁A.symm.trans (h ▸ hgB))
  have h₂ne : g₂ ≠ g := by
    intro h
    exact (FivePathState.middle_not_incident_first_edge G s hgL hg1)
      (h ▸ hg₂2)
  have h₃ne : g₃ ≠ g := by
    intro h
    exact hab (hg₃A.symm.trans (h ▸ hgB))
  have hrne : r ≠ g := by
    intro h
    exact hcb (hrC.symm.trans (h ▸ hgB))
  have h₁F : g₁ ∈ F.erase g :=
    Finset.mem_erase.mpr ⟨h₁ne, (Finset.mem_erase.mp hg₁F).2⟩
  have h₂F : g₂ ∈ F.erase g :=
    Finset.mem_erase.mpr ⟨h₂ne, (Finset.mem_erase.mp hg₂F).2⟩
  have h₃F : g₃ ∈ F.erase g :=
    Finset.mem_erase.mpr ⟨h₃ne, (Finset.mem_erase.mp hg₃F).2⟩
  have hrNew : r ∈ F.erase g :=
    Finset.mem_erase.mpr ⟨hrne, (Finset.mem_erase.mp hrF).2⟩
  have h₁shift : shifted g₁ = a := by
    simpa [shifted, G.assignEdgeColor_of_ne s.paint
      (Finset.mem_erase.mp hg₁F).1 b] using hg₁A
  have h₂shift : shifted g₂ = b := by
    simpa [shifted, G.assignEdgeColor_of_ne s.paint
      (Finset.mem_erase.mp hg₂F).1 b] using hg₂B
  have h₃shift : shifted g₃ = a := by
    simpa [shifted, G.assignEdgeColor_of_ne s.paint
      (Finset.mem_erase.mp hg₃F).1 b] using hg₃A
  have hrShift : shifted r = c := by
    simpa [shifted, G.assignEdgeColor_of_ne s.paint
      (Finset.mem_erase.mp hrF).1 b] using hrC
  have h₁sw : switched g₁ = a := by
    simpa [shifted, h₁shift] using
      hother g₁ (by simpa [shifted, h₁shift] using hab)
        (by simpa [shifted, h₁shift] using hac)
  have h₂sw : switched g₂ = b := by
    exact (hstable _ hZ2out g₂ h₂F hg₂2).trans h₂shift
  have h₃sw : switched g₃ = a := by
    simpa [shifted, h₃shift] using
      hother g₃ (by simpa [shifted, h₃shift] using hab)
        (by simpa [shifted, h₃shift] using hac)
  have hrSw : switched r = b :=
    hrightSwap r hrNew hrR hrShift
  let H := G.twoColorGraph (F.erase g) switched b a
  have hlen := s.path_len
  have hZ12 : H.Adj (s.path.1.getVert 1) (s.path.1.getVert 2) := by
    have hne : s.path.1.getVert 1 ≠ s.path.1.getVert 2 := by
      exact (s.path.1.adj_getVert_succ (i := 1) (by omega)).ne
    exact G.twoColorGraph_adj_of_witness_inc hne h₁F hg₁1 hg₁2
      (Or.inr h₁sw)
  have hZ23 : H.Adj (s.path.1.getVert 2) (s.path.1.getVert 3) := by
    have hne : s.path.1.getVert 2 ≠ s.path.1.getVert 3 := by
      exact (s.path.1.adj_getVert_succ (i := 2) (by omega)).ne
    exact G.twoColorGraph_adj_of_witness_inc hne h₂F hg₂2 hg₂3
      (Or.inl h₂sw)
  have hZ3R : H.Adj (s.path.1.getVert 3) s.right := by
    have hne : s.path.1.getVert 3 ≠ s.right := by
      have hlast : s.path.1.getVert 4 = s.right := by
        simpa [hlen] using s.path.1.getVert_length
      simpa [hlast] using
        (s.path.1.adj_getVert_succ (i := 3) (by omega)).ne
    exact G.twoColorGraph_adj_of_witness_inc hne h₃F hg₃3 hg₃R
      (Or.inr h₃sw)
  have hRW : H.Adj s.right w :=
    G.twoColorGraph_adj_of_witness_inc hwNeR.symm hrNew hrR hrw
      (Or.inl hrSw)
  have hZ1L : s.path.1.getVert 1 ≠ s.left := by
    intro h
    have hidx := s.path.property.getVert_injOn
      (Set.mem_Iic.mpr (by omega : 1 ≤ s.path.1.length))
      (Set.mem_Iic.mpr (by omega : 0 ≤ s.path.1.length))
      (by simpa using h)
    omega
  have hcomp := G.critical_endpoints_same_twoColorComponent_at
    hcritical (Finset.mem_erase.mp hgF).2 hproper hZ1L hg1 hgL hb ha
  have hreach : H.Reachable (s.path.1.getVert 1) s.left :=
    SimpleGraph.ConnectedComponent.exact hcomp
  obtain ⟨walk⟩ := hreach
  let q := walk.toPath
  have hC12 := SimpleGraph.ConnectedComponent.connectedComponentMk_eq_of_adj hZ12
  have hC23 := SimpleGraph.ConnectedComponent.connectedComponentMk_eq_of_adj hZ23
  have hC3R := SimpleGraph.ConnectedComponent.connectedComponentMk_eq_of_adj hZ3R
  have hCRW := SimpleGraph.ConnectedComponent.connectedComponentMk_eq_of_adj hRW
  have hZ2comp : H.connectedComponentMk (s.path.1.getVert 2) =
      H.connectedComponentMk (s.path.1.getVert 1) := hC12.symm
  have hZ3comp : H.connectedComponentMk (s.path.1.getVert 3) =
      H.connectedComponentMk (s.path.1.getVert 1) :=
    hC23.symm.trans hZ2comp
  have hRcomp : H.connectedComponentMk s.right =
      H.connectedComponentMk (s.path.1.getVert 1) :=
    hC3R.symm.trans hZ3comp
  have hLcomp : H.connectedComponentMk s.left =
      H.connectedComponentMk (s.path.1.getVert 1) := hcomp.symm
  have hwComp : H.connectedComponentMk w =
      H.connectedComponentMk (s.path.1.getVert 1) :=
    hCRW.symm.trans hRcomp
  have hlast : s.path.1.getVert 4 = s.right := by
    simpa [hlen] using s.path.1.getVert_length
  have hAll : ∀ v ∈ s.path.1.support,
      H.connectedComponentMk v =
        H.connectedComponentMk (s.path.1.getVert 1) := by
    intro v hv
    obtain ⟨i, hi, hiLe⟩ :=
      SimpleGraph.Walk.mem_support_iff_exists_getVert.mp hv
    subst v
    have hi4 : i ≤ 4 := by simpa [hlen] using hiLe
    interval_cases i
    · simpa using hLcomp
    · rfl
    · exact hZ2comp
    · exact hZ3comp
    · simpa [hlast] using hRcomp
  exact G.criticalPath_not_contains_fivePath_and_external_at
    s hcritical (Finset.mem_erase.mp hgF).2 hproper
    hZ1L hg1 hgL hb ha q hdk hdegree hthreshold hAll hwOut hwComp

end WeightedEdgeColoring.WeightedMultigraph
