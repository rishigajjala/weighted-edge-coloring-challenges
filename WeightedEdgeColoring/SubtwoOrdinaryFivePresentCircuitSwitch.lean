import WeightedEdgeColoring.SubtwoOrdinaryFivePresentCircuit

/-!
# Switching the circuit created in Andersen's `V = X` case
-/

namespace WeightedEdgeColoring.WeightedMultigraph

universe u
variable (G : WeightedMultigraph.{u})

noncomputable local instance fiveCircuitSwitchFiniteNeighborSet
    (H : SimpleGraph G.V) (v : G.V) : Fintype (H.neighborSet v) :=
  @Subtype.fintype G.V (fun w ↦ w ∈ H.neighborSet v)
    (Classical.decPred _) G.instFintypeV

/-- The `V = X` component closes into a circuit and may then be switched
without touching any edge incident with a vertex outside its support. -/
theorem FivePathState.exists_first_hit_left_circuit_switch
    {F : Finset G.E} {k : ℕ} {a b c : Fin k}
    (s : G.FivePathState F k a b)
    (hleft : FivePathState.HasExternalColorAt G s c s.left)
    (hright : FivePathState.HasExternalColorAt G s c s.right)
    (p : (G.twoColorGraph (F.erase s.omitted) s.paint b c).Path
      s.right s.left)
    (hfirstHit : s.path.1.getVert 1 ∉ p.1.support) :
    ∃ g : G.E, g ∈ F.erase s.omitted ∧
      G.Inc s.left g ∧ G.Inc (s.path.1.getVert 1) g ∧
      s.paint g = b ∧
      ∃ switched : G.E → Fin k,
        G.IsProperOn (F.erase g) switched ∧
        a ∈ G.missingColorsAt (F.erase g) switched s.left ∧
        (∀ r, G.assignEdgeColor s.paint s.omitted b r ≠ b →
          G.assignEdgeColor s.paint s.omitted b r ≠ c →
            switched r = G.assignEdgeColor s.paint s.omitted b r) ∧
        (∀ v, v ∉ p.1.support →
          ∀ r ∈ F.erase g, G.Inc v r →
            switched r = G.assignEdgeColor s.paint s.omitted b r) ∧
        (∀ r ∈ F.erase g, G.Inc s.right r →
          G.assignEdgeColor s.paint s.omitted b r = c →
            switched r = b) := by
  classical
  obtain ⟨g, hgF, hgL, hg1, hgB, hproper,
      q, hsupport, hlength, _, _, _⟩ :=
    FivePathState.first_hit_left_component_closes_after_shift
      G s hright p hfirstHit
  let shifted := G.assignEdgeColor s.paint s.omitted b
  let H := G.twoColorGraph (F.erase g) shifted b c
  have hpLen : 2 ≤ p.1.length := by
    apply G.path_length_at_least_two_of_no_endpoint_edge
      (G.twoColorGraph (F.erase s.omitted) s.paint b c) p
      s.left_ne_right.symm
    intro hadj
    exact (FivePathState.no_endpoint_bc_edge_of_external_right G s hright)
      hadj.symm
  have hqLen : 2 ≤ q.1.length := by omega
  have heFg : s.omitted ∈ F.erase g :=
    Finset.mem_erase.mpr
      ⟨Ne.symm (Finset.mem_erase.mp hgF).1, s.omitted_mem⟩
  have hnewE : shifted s.omitted = b := by
    simp [shifted, assignEdgeColor]
  have hXY : H.Adj s.right s.left :=
    G.twoColorGraph_adj_of_witness_inc s.left_ne_right.symm
      heFg s.right_inc s.left_inc (Or.inl hnewE)
  have hmax : ∀ v, H.degree v ≤ 2 := by
    intro v
    exact G.twoColorGraph_degree_le_two_of_isProperOn
      (F.erase g) shifted hproper b c v
  have hrightLeft : H.connectedComponentMk s.right =
      H.connectedComponentMk s.left :=
    SimpleGraph.ConnectedComponent.connectedComponentMk_eq_of_adj hXY
  have hcomponent : ∀ v, H.connectedComponentMk v =
      H.connectedComponentMk s.left → v ∈ p.1.support := by
    intro v hv
    have hvRight : H.connectedComponentMk v =
        H.connectedComponentMk s.right := hv.trans hrightLeft.symm
    have hmem := G.mem_closedPath_support_of_same_component
      H q hqLen hXY hmax hvRight
    simpa only [hsupport] using hmem
  let flip : H.ConnectedComponent → Prop :=
    fun C ↦ C = H.connectedComponentMk s.left
  letI : DecidablePred flip := Classical.decPred _
  let switched : G.E → Fin k :=
    G.kempeComponentSwitch (F.erase g) shifted b c flip
  have hproperSwitched : G.IsProperOn (F.erase g) switched :=
    G.isProperOn_kempeComponentSwitch (F.erase g) shifted hproper b c flip
  have hab : a ≠ b := by
    intro h
    have hne : s.paint g ≠ a :=
      G.color_ne_of_mem_missingColorsAt
        (F.erase s.omitted) s.paint s.left a s.left_missing hgF hgL
    exact hne (hgB.trans h.symm)
  have hac : a ≠ c :=
    Ne.symm (FivePathState.external_endpoint_color_ne_missing
      G s hleft hright).1
  have haShift : a ∈ G.missingColorsAt (F.erase g) shifted s.left :=
    G.mem_missingColorsAt_shiftOmitted_of_ne hab s.left_missing
  have haSwitched : a ∈ G.missingColorsAt (F.erase g) switched s.left :=
    (G.mem_missingColorsAt_kempeComponentSwitch_of_fixedColor_iff
      shifted b c flip s.left a hab hac).mpr haShift
  have hother : ∀ r, shifted r ≠ b → shifted r ≠ c →
      switched r = shifted r := by
    intro r hrb hrc
    exact G.kempeComponentSwitch_eq_of_color_ne
      shifted b c flip r hrb hrc
  have hstable : ∀ v, v ∉ p.1.support →
      ∀ r ∈ F.erase g, G.Inc v r → switched r = shifted r := by
    intro v hvOut r hrF hrV
    have hnot : ¬flip (H.connectedComponentMk v) := by
      intro h
      exact hvOut (hcomponent v h)
    change G.kempeComponentSwitch (F.erase g) shifted b c flip r =
      shifted r
    rw [G.kempeComponentSwitch_eq_localPerm
      (F.erase g) shifted b c flip hrF hrV]
    simp [kempeLocalPerm, flip, H, hnot]
  have hrightFlip : flip (H.connectedComponentMk s.right) :=
    hrightLeft
  have hrightSwap : ∀ r ∈ F.erase g, G.Inc s.right r →
      shifted r = c → switched r = b := by
    intro r hrF hrR hrc
    change G.kempeComponentSwitch (F.erase g) shifted b c flip r = b
    rw [G.kempeComponentSwitch_eq_localPerm
      (F.erase g) shifted b c flip hrF hrR]
    simp [kempeLocalPerm, H, hrightFlip, hrc]
  exact ⟨g, hgF, hgL, hg1, hgB,
    switched, hproperSwitched, haSwitched, hother, hstable, hrightSwap⟩

/-- The first-edge omitted-edge shift gives the opposite missing
palettes at `Z₁` and `X`, independently of the stored orientation of
the original omitted edge. -/
theorem FivePathState.first_shift_missing_palettes
    {F : Finset G.E} {k : ℕ} {a b : Fin k}
    (s : G.FivePathState F k a b)
    {g : G.E} (hgF : g ∈ F.erase s.omitted)
    (hgL : G.Inc s.left g)
    (hg1 : G.Inc (s.path.1.getVert 1) g)
    (hgB : s.paint g = b) :
    a ∈ G.missingColorsAt (F.erase g)
      (G.assignEdgeColor s.paint s.omitted b) s.left ∧
    b ∈ G.missingColorsAt (F.erase g)
      (G.assignEdgeColor s.paint s.omitted b)
      (s.path.1.getVert 1) := by
  have hab : a ≠ b := by
    intro h
    have hne : s.paint g ≠ a :=
      G.color_ne_of_mem_missingColorsAt
        (F.erase s.omitted) s.paint s.left a s.left_missing hgF hgL
    exact hne (hgB.trans h.symm)
  have haShift : a ∈ G.missingColorsAt (F.erase g)
      (G.assignEdgeColor s.paint s.omitted b) s.left :=
    G.mem_missingColorsAt_shiftOmitted_of_ne hab s.left_missing
  have hZ1neL : s.path.1.getVert 1 ≠ s.left := by
    intro h
    have hidx := s.path.property.getVert_injOn
      (Set.mem_Iic.mpr (by have hlen := s.path_len; omega : 1 ≤ s.path.1.length))
      (Set.mem_Iic.mpr (by omega : 0 ≤ s.path.1.length))
      (by simpa using h)
    omega
  have hZ1neR : s.path.1.getVert 1 ≠ s.right := by
    intro h
    have hlast : s.path.1.getVert 4 = s.right := by
      simpa [s.path_len] using s.path.1.getVert_length
    have hidx := s.path.property.getVert_injOn
      (Set.mem_Iic.mpr (by have hlen := s.path_len; omega : 1 ≤ s.path.1.length))
      (Set.mem_Iic.mpr (by have hlen := s.path_len; omega : 4 ≤ s.path.1.length))
      (h.trans hlast.symm)
    omega
  have hnotInc : ¬G.Inc (s.path.1.getVert 1) s.omitted := by
    have hends := G.endpoint_eq_or_endpoint_eq_swap_of_inc
      s.left_ne_right s.left_inc s.right_inc
    intro hinc
    rcases hends with ⟨hfst, hsnd⟩ | ⟨hfst, hsnd⟩
    · rcases hinc with h | h
      · exact hZ1neL (h.symm.trans hfst)
      · exact hZ1neR (h.symm.trans hsnd)
    · rcases hinc with h | h
      · exact hZ1neR (h.symm.trans hfst)
      · exact hZ1neL (h.symm.trans hsnd)
  have hbDouble : b ∈ G.missingColorsAt
      ((F.erase s.omitted).erase g) s.paint
      (s.path.1.getVert 1) := by
    simpa [hgB] using
      (G.mem_missingColorsAt_erase_of_edgeColor s.proper hgF hg1)
  have herase : (F.erase g).erase s.omitted =
      (F.erase s.omitted).erase g := by
    ext r
    simp [and_left_comm]
  have heFg : s.omitted ∈ F.erase g :=
    Finset.mem_erase.mpr
      ⟨Ne.symm (Finset.mem_erase.mp hgF).1, s.omitted_mem⟩
  have hbDouble' : b ∈ G.missingColorsAt
      ((F.erase g).erase s.omitted) s.paint
      (s.path.1.getVert 1) := by
    simpa [herase] using hbDouble
  have hbShift : b ∈ G.missingColorsAt (F.erase g)
      (G.assignEdgeColor s.paint s.omitted b)
      (s.path.1.getVert 1) :=
    G.mem_missingColorsAt_assignEdgeColor_of_not_inc
      heFg hnotInc hbDouble'
  exact ⟨haShift, hbShift⟩

/-- After switching the closed circuit, `b` is still absent at `Z₁`
and `a` remains absent at `X`; hence this is another valid critical
endpoint pair for the shifted omitted edge. -/
theorem FivePathState.exists_first_hit_left_circuit_switch_palettes
    {F : Finset G.E} {k : ℕ} {a b c : Fin k}
    (s : G.FivePathState F k a b)
    (hleft : FivePathState.HasExternalColorAt G s c s.left)
    (hright : FivePathState.HasExternalColorAt G s c s.right)
    (p : (G.twoColorGraph (F.erase s.omitted) s.paint b c).Path
      s.right s.left)
    (hfirstHit : s.path.1.getVert 1 ∉ p.1.support) :
    ∃ g : G.E, g ∈ F.erase s.omitted ∧
      G.Inc s.left g ∧ G.Inc (s.path.1.getVert 1) g ∧
      s.paint g = b ∧
      ∃ switched : G.E → Fin k,
        G.IsProperOn (F.erase g) switched ∧
        b ∈ G.missingColorsAt (F.erase g) switched
          (s.path.1.getVert 1) ∧
        a ∈ G.missingColorsAt (F.erase g) switched s.left ∧
        (∀ r, G.assignEdgeColor s.paint s.omitted b r ≠ b →
          G.assignEdgeColor s.paint s.omitted b r ≠ c →
            switched r = G.assignEdgeColor s.paint s.omitted b r) ∧
        (∀ v, v ∉ p.1.support →
          ∀ r ∈ F.erase g, G.Inc v r →
            switched r = G.assignEdgeColor s.paint s.omitted b r) ∧
        (∀ r ∈ F.erase g, G.Inc s.right r →
          G.assignEdgeColor s.paint s.omitted b r = c →
            switched r = b) := by
  classical
  obtain ⟨g, hgF, hgL, hg1, hgB,
      switched, hproper, ha, hother, hstable, hrightSwap⟩ :=
    FivePathState.exists_first_hit_left_circuit_switch
      G s hleft hright p hfirstHit
  have hbShift :=
    (FivePathState.first_shift_missing_palettes G s hgF hgL hg1 hgB).2
  have hbSwitched : b ∈ G.missingColorsAt (F.erase g) switched
      (s.path.1.getVert 1) := by
    simp only [missingColorsAt, Finset.mem_sdiff, Finset.mem_univ,
      true_and, Finset.mem_image] at hbShift ⊢
    intro hused
    obtain ⟨r, hr, hrc⟩ := hused
    have hrData := Finset.mem_filter.mp hr
    apply hbShift
    refine ⟨r, hr, ?_⟩
    exact (hstable _ hfirstHit r hrData.1 hrData.2).symm.trans hrc
  exact ⟨g, hgF, hgL, hg1, hgB, switched, hproper,
    hbSwitched, ha, hother, hstable, hrightSwap⟩

/-- At either orientation of an omitted critical edge, the two endpoints
have degree at most one in their critical two-color component. -/
theorem critical_endpoints_twoColorActive_at
    {F : Finset G.E} {k : ℕ} (hcritical : G.IsColorCriticalOn F k)
    {e : G.E} (heF : e ∈ F) {paint : G.E → Fin k}
    (hproper : G.IsProperOn (F.erase e) paint)
    {x y : G.V} (hxy : x ≠ y) (hxe : G.Inc x e) (hye : G.Inc y e)
    {a b : Fin k}
    (ha : a ∈ G.missingColorsAt (F.erase e) paint x)
    (hb : b ∈ G.missingColorsAt (F.erase e) paint y) :
    G.IsTwoColorActive (F.erase e) paint a b x ∧
      G.IsTwoColorActive (F.erase e) paint a b y := by
  have hends := G.endpoint_eq_or_endpoint_eq_swap_of_inc hxy hxe hye
  rcases hends with ⟨hfst, hsnd⟩ | ⟨hfst, hsnd⟩
  · have hpair := G.critical_endpoints_twoColorActive
      hcritical heF hproper
      (by simpa [hfst] using ha) (by simpa [hsnd] using hb)
    exact ⟨by simpa [hfst] using hpair.1,
      by simpa [hsnd] using hpair.2⟩
  · have hpair := G.critical_endpoints_twoColorActive
      hcritical heF hproper
      (by simpa [hfst] using hb) (by simpa [hsnd] using ha)
    exact ⟨by simpa [IsTwoColorActive, hsnd, or_comm] using hpair.2,
      by simpa [IsTwoColorActive, hfst, or_comm] using hpair.1⟩

/-- A critical two-color path between either orientation of an omitted
edge contains the whole connected component of either endpoint. -/
theorem mem_criticalPath_support_of_same_twoColorComponent_at
    {F : Finset G.E} {k : ℕ} (hcritical : G.IsColorCriticalOn F k)
    {e : G.E} (heF : e ∈ F) {paint : G.E → Fin k}
    (hproper : G.IsProperOn (F.erase e) paint)
    {x y : G.V} (hxy : x ≠ y) (hxe : G.Inc x e) (hye : G.Inc y e)
    {a b : Fin k}
    (ha : a ∈ G.missingColorsAt (F.erase e) paint x)
    (hb : b ∈ G.missingColorsAt (F.erase e) paint y)
    (q : (G.twoColorGraph (F.erase e) paint a b).Path x y)
    {v : G.V}
    (hcomp : (G.twoColorGraph (F.erase e) paint a b).connectedComponentMk v =
      (G.twoColorGraph (F.erase e) paint a b).connectedComponentMk x) :
    v ∈ q.1.support := by
  let H := G.twoColorGraph (F.erase e) paint a b
  have hlen : 0 < q.1.length := by
    by_contra h
    have hz : q.1.length = 0 := by omega
    exact hxy (SimpleGraph.Walk.eq_of_length_eq_zero hz)
  have hmax : ∀ z, H.degree z ≤ 2 := by
    intro z
    exact G.twoColorGraph_degree_le_two_of_isProperOn
      (F.erase e) paint hproper a b z
  have hactive := G.critical_endpoints_twoColorActive_at
    hcritical heF hproper hxy hxe hye ha hb
  have hx : H.degree x ≤ 1 :=
    G.twoColorGraph_degree_le_one_of_active
      (F.erase e) paint hproper a b x hactive.1
  have hy : H.degree y ≤ 1 :=
    G.twoColorGraph_degree_le_one_of_active
      (F.erase e) paint hproper a b y hactive.2
  have hreach : H.Reachable x v :=
    SimpleGraph.ConnectedComponent.exact hcomp.symm
  exact G.path_support_of_reachable_of_degree_le_two
    H q hlen hmax hx hy hreach

/-- The three surviving internal edges of the old five-path have the
alternating colors `a,b,a`. -/
theorem FivePathState.exists_three_surviving_path_edges
    {F : Finset G.E} {k : ℕ} {a b : Fin k}
    (s : G.FivePathState F k a b) :
    ∃ g₁ g₂ g₃ : G.E,
      g₁ ∈ F.erase s.omitted ∧
      G.Inc (s.path.1.getVert 1) g₁ ∧
      G.Inc (s.path.1.getVert 2) g₁ ∧ s.paint g₁ = a ∧
      g₂ ∈ F.erase s.omitted ∧
      G.Inc (s.path.1.getVert 2) g₂ ∧
      G.Inc (s.path.1.getVert 3) g₂ ∧ s.paint g₂ = b ∧
      g₃ ∈ F.erase s.omitted ∧
      G.Inc (s.path.1.getVert 3) g₃ ∧
      G.Inc s.right g₃ ∧ s.paint g₃ = a := by
  have hlen := s.path_len
  have hadj0 : (G.twoColorGraph (F.erase s.omitted) s.paint a b).Adj
      s.left (s.path.1.getVert 1) := by
    simpa using s.path.1.adj_getVert_succ (i := 0) (by omega)
  have hadj1 : (G.twoColorGraph (F.erase s.omitted) s.paint a b).Adj
      (s.path.1.getVert 1) (s.path.1.getVert 2) := by
    simpa using s.path.1.adj_getVert_succ (i := 1) (by omega)
  have hadj2 : (G.twoColorGraph (F.erase s.omitted) s.paint a b).Adj
      (s.path.1.getVert 2) (s.path.1.getVert 3) := by
    simpa using s.path.1.adj_getVert_succ (i := 2) (by omega)
  have hp4 : s.path.1.getVert 4 = s.right := by
    simpa [hlen] using s.path.1.getVert_length
  have hadj3 : (G.twoColorGraph (F.erase s.omitted) s.paint a b).Adj
      (s.path.1.getVert 3) s.right := by
    simpa [hp4] using s.path.1.adj_getVert_succ (i := 3) (by omega)
  obtain ⟨g₀, hg₀F, hg₀L, hg₀1, hg₀Color⟩ :=
    G.exists_twoColorWitnessEdge (F.erase s.omitted) s.paint a b hadj0
  obtain ⟨g₁, hg₁F, hg₁1, hg₁2, hg₁Color⟩ :=
    G.exists_twoColorWitnessEdge (F.erase s.omitted) s.paint a b hadj1
  obtain ⟨g₂, hg₂F, hg₂2, hg₂3, hg₂Color⟩ :=
    G.exists_twoColorWitnessEdge (F.erase s.omitted) s.paint a b hadj2
  obtain ⟨g₃, hg₃F, hg₃3, hg₃R, hg₃Color⟩ :=
    G.exists_twoColorWitnessEdge (F.erase s.omitted) s.paint a b hadj3
  have hg₀NeA : s.paint g₀ ≠ a :=
    G.color_ne_of_mem_missingColorsAt
      (F.erase s.omitted) s.paint s.left a s.left_missing hg₀F hg₀L
  have hg₀B : s.paint g₀ = b := hg₀Color.resolve_left hg₀NeA
  have hne01 := G.path_witness_colors_ne s.proper s.path 0
    (by omega) hg₀F hg₁F (by simpa using hg₀L) hg₀1 hg₁1 hg₁2
  have hg₁NeB : s.paint g₁ ≠ b := by
    intro h
    exact hne01 (hg₀B.trans h.symm)
  have hg₁A : s.paint g₁ = a := hg₁Color.resolve_right hg₁NeB
  have hg₃NeB : s.paint g₃ ≠ b :=
    G.color_ne_of_mem_missingColorsAt
      (F.erase s.omitted) s.paint s.right b s.right_missing hg₃F hg₃R
  have hg₃A : s.paint g₃ = a := hg₃Color.resolve_right hg₃NeB
  have hne23 := G.path_witness_colors_ne s.proper s.path 2
    (by omega) hg₂F hg₃F hg₂2 hg₂3 hg₃3 (by simpa [hp4] using hg₃R)
  have hg₂NeA : s.paint g₂ ≠ a := by
    intro h
    exact hne23 (h.trans hg₃A.symm)
  have hg₂B : s.paint g₂ = b := hg₂Color.resolve_left hg₂NeA
  exact ⟨g₁, g₂, g₃,
    hg₁F, hg₁1, hg₁2, hg₁A,
    hg₂F, hg₂2, hg₂3, hg₂B,
    hg₃F, hg₃3, hg₃R, hg₃A⟩

/-- Under the seven-sixths threshold, any critical path between either
orientation of an omitted edge has at most five vertices. -/
theorem criticalPath_support_card_le_five_at
    {F : Finset G.E} {k d : ℕ} (hcritical : G.IsColorCriticalOn F k)
    {e : G.E} (heF : e ∈ F) {paint : G.E → Fin k}
    (hproper : G.IsProperOn (F.erase e) paint)
    {x y : G.V} (hxy : x ≠ y) (hxe : G.Inc x e) (hye : G.Inc y e)
    {a b : Fin k}
    (ha : a ∈ G.missingColorsAt (F.erase e) paint x)
    (hb : b ∈ G.missingColorsAt (F.erase e) paint y)
    (q : (G.twoColorGraph (F.erase e) paint a b).Path x y)
    (hdk : d + 1 < k) (hdegree : ∀ z, G.degreeOn F z ≤ d)
    (hthreshold : 7 * d < 6 * k + 2) :
    q.1.support.toFinset.card ≤ 5 := by
  have hends := G.endpoint_eq_or_endpoint_eq_swap_of_inc hxy hxe hye
  rcases hends with ⟨hfst, hsnd⟩ | ⟨hfst, hsnd⟩
  · let q0 := G.pathEndpointsCast hfst hsnd q
    have hsupport : q0.1.support.toFinset = q.1.support.toFinset := by
      rw [G.pathEndpointsCast_support]
    have ha0 : a ∈ G.missingColorsAt (F.erase e) paint (G.fst e) := by
      simpa [hfst] using ha
    have hb0 : b ∈ G.missingColorsAt (F.erase e) paint (G.snd e) := by
      simpa [hsnd] using hb
    have hcard := G.criticalPath_support_card_eq_three_or_five
      hcritical heF hproper ha0 hb0 q0
      (by omega : d < k) hdegree hthreshold
    rw [hsupport] at hcard
    omega
  · let R := G.reverseEndpoints
    have hgraph : R.twoColorGraph (F.erase e) paint a b =
        G.twoColorGraph (F.erase e) paint a b := by
      exact (G.reverseEndpoints_twoColorGraph paint b a
        (F := F.erase e)).trans
        (G.twoColorGraph_swap paint b a (F := F.erase e))
    let q1 := G.pathCast hgraph q
    have hRf : R.fst e = x := by simpa [R] using hsnd
    have hRs : R.snd e = y := by simpa [R] using hfst
    let qR := G.pathEndpointsCast hRf hRs q1
    have hsupport : qR.1.support.toFinset = q.1.support.toFinset := by
      rw [G.pathEndpointsCast_support, G.pathCast_support]
    have hproperR : R.IsProperOn (F.erase e) paint :=
      G.reverseEndpoints_proper_iff.mpr hproper
    have hcriticalR : R.IsColorCriticalOn F k :=
      G.reverseEndpoints_critical_iff.mpr hcritical
    have hdegreeR : ∀ z, R.degreeOn F z ≤ d := by
      intro z
      simpa [R] using hdegree z
    have haR : a ∈ R.missingColorsAt (F.erase e) paint (R.fst e) := by
      simpa [R, hRf] using ha
    have hbR : b ∈ R.missingColorsAt (F.erase e) paint (R.snd e) := by
      simpa [R, hRs] using hb
    have hcard := R.criticalPath_support_card_eq_three_or_five
      hcriticalR heF hproperR haR hbR qR
      (by omega : d < k) hdegreeR hthreshold
    rw [hsupport] at hcard
    omega

end WeightedEdgeColoring.WeightedMultigraph
