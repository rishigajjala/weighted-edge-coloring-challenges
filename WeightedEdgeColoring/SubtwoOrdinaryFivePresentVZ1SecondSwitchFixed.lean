import WeightedEdgeColoring.SubtwoOrdinaryFivePresentDSecondEdge

/-!
# Fixed-color palettes through the second V=Z1 switch
-/

namespace WeightedEdgeColoring.WeightedMultigraph

universe u
variable (G : WeightedMultigraph.{u})

/-- The first `(a,b)` switch preserves whether any other color is
missing at the old left endpoint. -/
theorem FivePathState.fixed_color_missing_left_after_ab_switch
    {F : Finset G.E} {k : ℕ} {a b d : Fin k}
    (s : G.FivePathState F k a b)
    {switched : G.E → Fin k}
    (hswapA : ∀ v ∈ s.path.1.support,
      ∀ r ∈ F.erase s.omitted, G.Inc v r →
        s.paint r = a → switched r = b)
    (hswapB : ∀ v ∈ s.path.1.support,
      ∀ r ∈ F.erase s.omitted, G.Inc v r →
        s.paint r = b → switched r = a)
    (hother : ∀ r, s.paint r ≠ a → s.paint r ≠ b →
      switched r = s.paint r)
    (hda : d ≠ a) (hdb : d ≠ b) :
    d ∈ G.missingColorsAt (F.erase s.omitted) switched s.left ↔
      d ∈ G.missingColorsAt (F.erase s.omitted) s.paint s.left := by
  have hleft : s.left ∈ s.path.1.support := s.path.1.start_mem_support
  have hcolor : ∀ r ∈ F.erase s.omitted,
      G.Inc s.left r → (switched r = d ↔ s.paint r = d) := by
    intro r hrF hrX
    by_cases hra : s.paint r = a
    · have hsw := hswapA s.left hleft r hrF hrX hra
      simp [hra, hsw, hda.symm, hdb.symm]
    by_cases hrb : s.paint r = b
    · have hsw := hswapB s.left hleft r hrF hrX hrb
      simp [hrb, hsw, hda.symm, hdb.symm]
    · rw [hother r hra hrb]
  simp only [missingColorsAt, Finset.mem_sdiff, Finset.mem_univ,
    true_and, Finset.mem_image]
  constructor
  · intro hsw ⟨r,hr,hpaint⟩
    have hrData := Finset.mem_filter.mp hr
    exact hsw ⟨r,hr,(hcolor r hrData.1 hrData.2).mpr hpaint⟩
  · intro hpaint ⟨r,hr,hsw⟩
    have hrData := Finset.mem_filter.mp hr
    exact hpaint ⟨r,hr,(hcolor r hrData.1 hrData.2).mp hsw⟩

noncomputable local instance vz1SecondFixedFiniteNeighborSet
    (H : SimpleGraph G.V) (v : G.V) : Fintype (H.neighborSet v) :=
  @Subtype.fintype G.V (fun w ↦ w ∈ H.neighborSet v)
    (Classical.decPred _) G.instFintypeV

theorem FivePathState.exists_second_switch_outside_right_circuit_fixed
    {F : Finset G.E} {k d : ℕ} {a b c : Fin k}
    (s : G.FivePathState F k a b)
    (hcritical : G.IsColorCriticalOn F k)
    (hdk : d + 1 < k) (hdegree : ∀ z, G.degreeOn F z ≤ d)
    (hthreshold : 7 * d < 6 * k + 2)
    {paint₁ : G.E → Fin k}
    (hproper₁ : G.IsProperOn (F.erase s.omitted) paint₁)
    (hbX : b ∈ G.missingColorsAt (F.erase s.omitted) paint₁ s.left)
    (haY : a ∈ G.missingColorsAt (F.erase s.omitted) paint₁ s.right)
    (q₂ : (G.twoColorGraph (F.erase s.omitted) paint₁ b c).Path
      s.right (s.path.1.getVert 3))
    (hqLen : 2 ≤ q₂.1.length)
    (hclose : (G.twoColorGraph (F.erase s.omitted) paint₁ b c).Adj
      (s.path.1.getVert 3) s.right)
    (hXout : s.left ∉ q₂.1.support) :
    ∃ paint₂ : G.E → Fin k,
      G.IsProperOn (F.erase s.omitted) paint₂ ∧
      c ∈ G.missingColorsAt (F.erase s.omitted) paint₂ s.left ∧
      a ∈ G.missingColorsAt (F.erase s.omitted) paint₂ s.right ∧
      (∀ r, paint₁ r ≠ b → paint₁ r ≠ c → paint₂ r = paint₁ r) ∧
      (∀ v ∈ q₂.1.support,
        ∀ r ∈ F.erase s.omitted, G.Inc v r → paint₂ r = paint₁ r) ∧
      (∀ d, d ≠ b → d ≠ c →
        (d ∈ G.missingColorsAt (F.erase s.omitted) paint₂ s.left ↔
          d ∈ G.missingColorsAt (F.erase s.omitted) paint₁ s.left)) ∧
      ∃ q : (G.twoColorGraph (F.erase s.omitted) paint₂ c a).Path
        s.left s.right,
        q.1.support.toFinset.card ≤ 5 := by
  classical
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
    fun C ↦ C = H.connectedComponentMk s.left
  letI : DecidablePred flip := Classical.decPred _
  let paint₂ := G.kempeComponentSwitch
    (F.erase s.omitted) paint₁ b c flip
  have hproper₂ : G.IsProperOn (F.erase s.omitted) paint₂ :=
    G.isProperOn_kempeComponentSwitch
      (F.erase s.omitted) paint₁ hproper₁ b c flip
  have hcX : c ∈ G.missingColorsAt (F.erase s.omitted) paint₂ s.left :=
    (G.mem_missingColorsAt_kempeComponentSwitch_of_flip
      (F.erase s.omitted) paint₁ b c flip s.left rfl).1.mpr hbX
  have hYnot : ¬flip (H.connectedComponentMk s.right) := by
    intro h
    exact hsep h.symm
  have haY₂ : a ∈ G.missingColorsAt (F.erase s.omitted) paint₂ s.right :=
    (G.mem_missingColorsAt_kempeComponentSwitch_of_not_flip_iff
      (F.erase s.omitted) paint₁ b c flip s.right hYnot a).mpr haY
  have hother : ∀ r, paint₁ r ≠ b → paint₁ r ≠ c →
      paint₂ r = paint₁ r := by
    intro r hrb hrc
    exact G.kempeComponentSwitch_eq_of_color_ne
      paint₁ b c flip r hrb hrc
  have hstable : ∀ v ∈ q₂.1.support,
      ∀ r ∈ F.erase s.omitted, G.Inc v r → paint₂ r = paint₁ r := by
    intro v hv r hrF hrV
    have hreach : H.Reachable s.right v :=
      ⟨q₂.1.takeUntil v hv⟩
    have hcomp : H.connectedComponentMk v =
        H.connectedComponentMk s.right :=
      (SimpleGraph.ConnectedComponent.sound hreach).symm
    have hnot : ¬flip (H.connectedComponentMk v) := by
      intro h
      exact hsep (h.symm.trans hcomp)
    change G.kempeComponentSwitch (F.erase s.omitted)
      paint₁ b c flip r = paint₁ r
    rw [G.kempeComponentSwitch_eq_localPerm
      (F.erase s.omitted) paint₁ b c flip hrF hrV]
    simp [kempeLocalPerm, flip, H, hnot]
  have hcompCA := G.critical_endpoints_same_twoColorComponent_at
    hcritical s.omitted_mem hproper₂ s.left_ne_right
    s.left_inc s.right_inc hcX haY₂
  have hreachCA : (G.twoColorGraph (F.erase s.omitted) paint₂ c a).Reachable
      s.left s.right := SimpleGraph.ConnectedComponent.exact hcompCA
  obtain ⟨walk⟩ := hreachCA
  let q := walk.toPath
  have hcard := G.criticalPath_support_card_le_five_at
    hcritical s.omitted_mem hproper₂ s.left_ne_right
    s.left_inc s.right_inc hcX haY₂ q
    hdk hdegree hthreshold
  have hfixed : ∀ d, d ≠ b → d ≠ c →
      (d ∈ G.missingColorsAt (F.erase s.omitted) paint₂ s.left ↔
        d ∈ G.missingColorsAt (F.erase s.omitted) paint₁ s.left) := by
    intro d hdb hdc
    exact G.mem_missingColorsAt_kempeComponentSwitch_of_fixedColor_iff
      (F := F.erase s.omitted) paint₁ b c flip s.left d hdb hdc
  exact ⟨paint₂, hproper₂, hcX, haY₂, hother, hstable,
    hfixed, q, hcard⟩


end WeightedEdgeColoring.WeightedMultigraph
