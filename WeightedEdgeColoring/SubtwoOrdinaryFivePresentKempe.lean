import WeightedEdgeColoring.SubtwoOrdinaryFivePresentStateColors

/-!
# The first endpoint component switch in the five-chain present-color case
-/

namespace WeightedEdgeColoring.WeightedMultigraph

universe u
variable (G : WeightedMultigraph.{u})

/-- A critical endpoint path in any oriented five-path state has three
or five vertices under the seven-sixths threshold. -/
theorem FivePathState.critical_path_card_three_or_five
    {F : Finset G.E} {k d : ℕ} {a b : Fin k}
    (s : G.FivePathState F k a b)
    (hcritical : G.IsColorCriticalOn F k)
    (hdk : d + 1 < k) (hdegree : ∀ z, G.degreeOn F z ≤ d)
    (hthreshold : 7 * d < 6 * k + 2)
    {paint : G.E → Fin k} (hproper : G.IsProperOn (F.erase s.omitted) paint)
    {x y : Fin k}
    (hx : x ∈ G.missingColorsAt (F.erase s.omitted) paint s.left)
    (hy : y ∈ G.missingColorsAt (F.erase s.omitted) paint s.right)
    (q : (G.twoColorGraph (F.erase s.omitted) paint x y).Path
      s.left s.right) :
    q.1.support.toFinset.card = 3 ∨ q.1.support.toFinset.card = 5 := by
  have hends := G.endpoint_eq_or_endpoint_eq_swap_of_inc
    s.left_ne_right s.left_inc s.right_inc
  rcases hends with ⟨hfst, hsnd⟩ | ⟨hfst, hsnd⟩
  · let q0 := G.pathEndpointsCast hfst hsnd q
    have hqSupport : q0.1.support.toFinset = q.1.support.toFinset := by
      rw [G.pathEndpointsCast_support]
    have hx0 : x ∈ G.missingColorsAt (F.erase s.omitted)
        paint (G.fst s.omitted) := by simpa [hfst] using hx
    have hy0 : y ∈ G.missingColorsAt (F.erase s.omitted)
        paint (G.snd s.omitted) := by simpa [hsnd] using hy
    have hcard := G.criticalPath_support_card_eq_three_or_five
      hcritical s.omitted_mem hproper hx0 hy0 q0
      (by omega : d < k) hdegree hthreshold
    simpa [hqSupport] using hcard
  · let R := G.reverseEndpoints
    have hgraph : R.twoColorGraph (F.erase s.omitted) paint x y =
        G.twoColorGraph (F.erase s.omitted) paint x y := by
      exact (G.reverseEndpoints_twoColorGraph paint y x
        (F := F.erase s.omitted)).trans
        (G.twoColorGraph_swap paint y x (F := F.erase s.omitted))
    let q1 := G.pathCast hgraph q
    have hRf : R.fst s.omitted = s.left := by simpa [R] using hsnd
    have hRs : R.snd s.omitted = s.right := by simpa [R] using hfst
    let qR := G.pathEndpointsCast hRf hRs q1
    have hqSupport : qR.1.support.toFinset = q.1.support.toFinset := by
      rw [G.pathEndpointsCast_support, G.pathCast_support]
    have hproperR : R.IsProperOn (F.erase s.omitted) paint :=
      G.reverseEndpoints_proper_iff.mpr hproper
    have hcriticalR : R.IsColorCriticalOn F k :=
      G.reverseEndpoints_critical_iff.mpr hcritical
    have hdegreeR : ∀ z, R.degreeOn F z ≤ d := by
      intro z
      simpa [R] using hdegree z
    have hxR : x ∈ R.missingColorsAt (F.erase s.omitted)
        paint (R.fst s.omitted) := by simpa [R, hRf] using hx
    have hyR : y ∈ R.missingColorsAt (F.erase s.omitted)
        paint (R.snd s.omitted) := by simpa [R, hRs] using hy
    have hcard := R.criticalPath_support_card_eq_three_or_five
      hcriticalR s.omitted_mem hproperR hxR hyR qR
      (by omega : d < k) hdegreeR hthreshold
    simpa [hqSupport] using hcard

/-- Switching the `(b,c)` component of the right endpoint makes `c`
missing there while retaining the missing color `a` at the left endpoint.
If the left endpoint is in a different component, all its incident colors
are unchanged. -/
theorem FivePathState.exists_right_component_switch
    {F : Finset G.E} {k : ℕ} {a b c : Fin k}
    (s : G.FivePathState F k a b)
    (hcritical : G.IsColorCriticalOn F k)
    (hleft : FivePathState.HasExternalColorAt G s c s.left)
    (hright : FivePathState.HasExternalColorAt G s c s.right) :
    ∃ switched : G.E → Fin k,
      G.IsProperOn (F.erase s.omitted) switched ∧
      a ∈ G.missingColorsAt (F.erase s.omitted) switched s.left ∧
      c ∈ G.missingColorsAt (F.erase s.omitted) switched s.right ∧
      (∀ g, s.paint g ≠ b → s.paint g ≠ c →
        switched g = s.paint g) ∧
      (∀ v, (G.twoColorGraph (F.erase s.omitted) s.paint b c).connectedComponentMk
          v ≠
        (G.twoColorGraph (F.erase s.omitted) s.paint b c).connectedComponentMk
          s.right →
        ∀ g ∈ F.erase s.omitted, G.Inc v g →
          switched g = s.paint g) ∧
      ((G.twoColorGraph (F.erase s.omitted) s.paint b c).connectedComponentMk
          s.left ≠
        (G.twoColorGraph (F.erase s.omitted) s.paint b c).connectedComponentMk
          s.right →
        ∀ g ∈ F.erase s.omitted, G.Inc s.left g →
          switched g = s.paint g) := by
  classical
  let R := F.erase s.omitted
  let H := G.twoColorGraph R s.paint b c
  let CY : H.ConnectedComponent := H.connectedComponentMk s.right
  let flip : H.ConnectedComponent → Prop := fun C ↦ C = CY
  letI : DecidablePred flip := Classical.decPred _
  let switched : G.E → Fin k :=
    G.kempeComponentSwitch R s.paint b c flip
  have hproperSwitched : G.IsProperOn R switched :=
    G.isProperOn_kempeComponentSwitch R s.paint s.proper b c flip
  have hcne := FivePathState.external_endpoint_color_ne_missing
    G s hleft hright
  have hab : a ≠ b := by
    intro h
    subst b
    have hends := G.endpoint_eq_or_endpoint_eq_swap_of_inc
      s.left_ne_right s.left_inc s.right_inc
    rcases hends with hdirect | hswap
    · exact G.not_both_mem_missingColorsAt_endpoints_of_colorCritical
        hcritical s.omitted_mem s.proper a
          ⟨by simpa [hdirect.1] using s.left_missing,
            by simpa [hdirect.2] using s.right_missing⟩
    · exact G.not_both_mem_missingColorsAt_endpoints_of_colorCritical
        hcritical s.omitted_mem s.proper a
          ⟨by simpa [hswap.1] using s.right_missing,
            by simpa [hswap.2] using s.left_missing⟩
  have hac : a ≠ c := Ne.symm hcne.1
  have hcb : c ≠ b := hcne.2
  have haSwitched : a ∈ G.missingColorsAt R switched s.left :=
    (G.mem_missingColorsAt_kempeComponentSwitch_of_fixedColor_iff
      s.paint b c flip s.left a hab hac).mpr s.left_missing
  have hyFlip : flip (H.connectedComponentMk s.right) := rfl
  have hcSwitched : c ∈ G.missingColorsAt R switched s.right :=
    (G.mem_missingColorsAt_kempeComponentSwitch_of_flip
      R s.paint b c flip s.right hyFlip).1.mpr s.right_missing
  have hother : ∀ g, s.paint g ≠ b → s.paint g ≠ c →
      switched g = s.paint g := by
    intro g hgb hgc
    exact G.kempeComponentSwitch_eq_of_color_ne s.paint b c flip g hgb hgc
  have hstable : ∀ v, H.connectedComponentMk v ≠ H.connectedComponentMk s.right →
      ∀ g ∈ R, G.Inc v g → switched g = s.paint g := by
    intro v hneq g hgF hgv
    change G.kempeComponentSwitch R s.paint b c flip g = s.paint g
    rw [G.kempeComponentSwitch_eq_localPerm R s.paint b c flip hgF hgv]
    have hn : ¬flip (H.connectedComponentMk v) := hneq
    simp [kempeLocalPerm, flip, H, hn]
  exact ⟨switched, hproperSwitched, haSwitched, hcSwitched,
    hother, hstable, hstable s.left⟩

/-- The switched endpoint palettes force a critical `(a,c)` path between
the omitted-edge endpoints, regardless of stored edge orientation. -/
theorem FivePathState.exists_right_switched_critical_path
    {F : Finset G.E} {k d : ℕ} {a b c : Fin k}
    (s : G.FivePathState F k a b)
    (hcritical : G.IsColorCriticalOn F k)
    (hdk : d + 1 < k) (hdegree : ∀ z, G.degreeOn F z ≤ d)
    (hthreshold : 7 * d < 6 * k + 2)
    (hleft : FivePathState.HasExternalColorAt G s c s.left)
    (hright : FivePathState.HasExternalColorAt G s c s.right) :
    ∃ switched : G.E → Fin k,
      G.IsProperOn (F.erase s.omitted) switched ∧
      a ∈ G.missingColorsAt (F.erase s.omitted) switched s.left ∧
      c ∈ G.missingColorsAt (F.erase s.omitted) switched s.right ∧
      (∀ g, s.paint g ≠ b → s.paint g ≠ c →
        switched g = s.paint g) ∧
      (∀ v, (G.twoColorGraph (F.erase s.omitted) s.paint b c).connectedComponentMk
          v ≠
        (G.twoColorGraph (F.erase s.omitted) s.paint b c).connectedComponentMk
          s.right →
        ∀ g ∈ F.erase s.omitted, G.Inc v g →
          switched g = s.paint g) ∧
      ((G.twoColorGraph (F.erase s.omitted) s.paint b c).connectedComponentMk
          s.left ≠
        (G.twoColorGraph (F.erase s.omitted) s.paint b c).connectedComponentMk
          s.right →
        ∀ g ∈ F.erase s.omitted, G.Inc s.left g →
          switched g = s.paint g) ∧
      ∃ q : (G.twoColorGraph (F.erase s.omitted) switched a c).Path
        s.left s.right,
        q.1.support.toFinset.card = 3 ∨
          q.1.support.toFinset.card = 5 := by
  obtain ⟨switched, hproper, ha, hc, hother, hstable, hleftStable⟩ :=
    FivePathState.exists_right_component_switch
      G s hcritical hleft hright
  have hcomp := G.critical_endpoints_same_twoColorComponent_at
    hcritical s.omitted_mem hproper s.left_ne_right
    s.left_inc s.right_inc ha hc
  have hreach : (G.twoColorGraph (F.erase s.omitted) switched a c).Reachable
      s.left s.right := SimpleGraph.ConnectedComponent.exact hcomp
  obtain ⟨w⟩ := hreach
  let q := w.toPath
  have hcard := FivePathState.critical_path_card_three_or_five G s
    hcritical hdk hdegree hthreshold hproper ha hc q
  exact ⟨switched, hproper, ha, hc, hother, hstable,
    hleftStable, q, hcard⟩

/-- If the right `(b,c)` component misses the left endpoint, the first
vertex of the resulting critical `(a,c)` path lies outside the original
five-path. -/
theorem FivePathState.first_switched_critical_path_vertex_outside
    {F : Finset G.E} {k d : ℕ} {a b c : Fin k}
    (s : G.FivePathState F k a b)
    (hcritical : G.IsColorCriticalOn F k)
    (hdk : d + 1 < k) (hdegree : ∀ z, G.degreeOn F z ≤ d)
    (hthreshold : 7 * d < 6 * k + 2)
    (hleft : FivePathState.HasExternalColorAt G s c s.left)
    (hright : FivePathState.HasExternalColorAt G s c s.right)
    (hseparate :
      (G.twoColorGraph (F.erase s.omitted) s.paint b c).connectedComponentMk
          s.left ≠
        (G.twoColorGraph (F.erase s.omitted) s.paint b c).connectedComponentMk
          s.right) :
    ∃ switched : G.E → Fin k,
      G.IsProperOn (F.erase s.omitted) switched ∧
      a ∈ G.missingColorsAt (F.erase s.omitted) switched s.left ∧
      c ∈ G.missingColorsAt (F.erase s.omitted) switched s.right ∧
      ∃ q : (G.twoColorGraph (F.erase s.omitted) switched a c).Path
        s.left s.right,
        q.1.support.toFinset.card = 5 ∧
        q.1.getVert 1 ∉ s.path.1.support.toFinset ∧
        q.1.getVert 3 = s.path.1.getVert 3 := by
  obtain ⟨g, hgF, hgL, hgc, hgExt⟩ := (show
    FivePathState.HasExternalColorAt G s c s.left from hleft)
  have hL : s.left ∈ s.path.1.support.toFinset := by
    simpa only [List.mem_toFinset] using s.path.1.start_mem_support
  obtain ⟨u, hgu, huOut, huNeL⟩ :=
    FivePathState.outside_neighbor_of_external_edge G s hL hgF hgExt
  obtain ⟨switched, hproper, ha, hc, hother, _, hleftStable, q, hcard⟩ :=
    FivePathState.exists_right_switched_critical_path G s hcritical
      hdk hdegree hthreshold hleft hright
  have hpos : 0 < q.1.length := by
    by_contra h
    have hz : q.1.length = 0 := by omega
    exact s.left_ne_right (SimpleGraph.Walk.eq_of_length_eq_zero hz)
  let z := q.1.getVert 1
  have hadj : (G.twoColorGraph (F.erase s.omitted) switched a c).Adj
      s.left z := by
    simpa [z] using q.1.adj_getVert_succ (i := 0) hpos
  obtain ⟨r, hrF, hrL, hrZ, hrColor⟩ :=
    G.exists_twoColorWitnessEdge (F.erase s.omitted) switched a c hadj
  have hrNeA : switched r ≠ a :=
    G.color_ne_of_mem_missingColorsAt
      (F.erase s.omitted) switched s.left a ha hrF hrL
  have hrc : switched r = c := hrColor.resolve_left hrNeA
  have hgNew : switched g = c := (hleftStable hseparate g hgF hgL).trans hgc
  have hrg : r = g := by
    apply hproper s.left
    · exact Finset.mem_coe.mpr (Finset.mem_filter.mpr ⟨hrF, hrL⟩)
    · exact Finset.mem_coe.mpr (Finset.mem_filter.mpr ⟨hgF, hgL⟩)
    · exact hrc.trans hgNew.symm
  have hzNeL : s.left ≠ z := hadj.ne
  have hotherQ := G.kempeOtherEndpoint_eq_of_incident hrL hrZ hzNeL
  have hotherU := G.kempeOtherEndpoint_eq_of_incident hgL hgu huNeL.symm
  rw [hrg] at hotherQ
  have hzu : z = u := hotherQ.symm.trans hotherU
  have hzOut : z ∉ s.path.1.support.toFinset := hzu ▸ huOut
  have hab : a ≠ b := by
    intro h
    subst b
    have hends := G.endpoint_eq_or_endpoint_eq_swap_of_inc
      s.left_ne_right s.left_inc s.right_inc
    rcases hends with hdirect | hswap
    · exact G.not_both_mem_missingColorsAt_endpoints_of_colorCritical
        hcritical s.omitted_mem s.proper a
          ⟨by simpa [hdirect.1] using s.left_missing,
            by simpa [hdirect.2] using s.right_missing⟩
    · exact G.not_both_mem_missingColorsAt_endpoints_of_colorCritical
        hcritical s.omitted_mem s.proper a
          ⟨by simpa [hswap.1] using s.right_missing,
            by simpa [hswap.2] using s.left_missing⟩
  have hac : a ≠ c :=
    Ne.symm (FivePathState.external_endpoint_color_ne_missing
      G s (by exact ⟨g, hgF, hgL, hgc, hgExt⟩) hright).1
  have hp4 : s.path.1.getVert 4 = s.right := by
    simpa [s.path_len] using s.path.1.getVert_length
  let t := s.path.1.getVert 3
  have hadjLast : (G.twoColorGraph (F.erase s.omitted) s.paint a b).Adj
      t s.right := by
    simpa [t, hp4] using
      s.path.1.adj_getVert_succ (i := 3)
        (by simpa [s.path_len] : 3 < s.path.1.length)
  obtain ⟨g3, hg3F, hg3T, hg3R, hg3Color⟩ :=
    G.exists_twoColorWitnessEdge (F.erase s.omitted) s.paint a b hadjLast
  have hg3NeB : s.paint g3 ≠ b :=
    G.color_ne_of_mem_missingColorsAt
      (F.erase s.omitted) s.paint s.right b s.right_missing hg3F hg3R
  have hg3A : s.paint g3 = a := hg3Color.resolve_right hg3NeB
  have hg3New : switched g3 = a := by
    have hg3NeC : s.paint g3 ≠ c := by simpa [hg3A] using hac
    rw [hother g3 hg3NeB hg3NeC, hg3A]
  have hnotThree : q.1.support.toFinset.card ≠ 3 := by
    intro hthree
    have hqLen : q.1.length = 2 := by
      have hcardLen : q.1.support.toFinset.card = q.1.length + 1 := by
        rw [List.toFinset_card_of_nodup q.property.support_nodup,
          q.1.length_support]
      omega
    have hq2 : q.1.getVert 2 = s.right := by
      simpa [hqLen] using q.1.getVert_length
    have hadjQ : (G.twoColorGraph (F.erase s.omitted) switched a c).Adj
        (q.1.getVert 1) s.right := by
      simpa [hq2] using q.1.adj_getVert_succ
        (i := 1) (by omega : 1 < q.1.length)
    obtain ⟨r, hrF, hr1, hrR, hrColor⟩ :=
      G.exists_twoColorWitnessEdge
        (F.erase s.omitted) switched a c hadjQ
    have hrNeC : switched r ≠ c :=
      G.color_ne_of_mem_missingColorsAt
        (F.erase s.omitted) switched s.right c hc hrF hrR
    have hrA : switched r = a := hrColor.resolve_right hrNeC
    have hrg3 : r = g3 := by
      apply hproper s.right
      · exact Finset.mem_coe.mpr (Finset.mem_filter.mpr ⟨hrF, hrR⟩)
      · exact Finset.mem_coe.mpr (Finset.mem_filter.mpr ⟨hg3F, hg3R⟩)
      · exact hrA.trans hg3New.symm
    have hqOther := G.kempeOtherEndpoint_eq_of_incident
      hrR hr1 hadjQ.ne.symm
    have hpOther := G.kempeOtherEndpoint_eq_of_incident
      hg3R hg3T hadjLast.ne.symm
    rw [hrg3] at hqOther
    have hqt : q.1.getVert 1 = t := hqOther.symm.trans hpOther
    exact hzOut (by simpa [z, hqt, t] using
      s.path.1.getVert_mem_support 3)
  have hfive : q.1.support.toFinset.card = 5 := hcard.resolve_left hnotThree
  have hqLen : q.1.length = 4 := by
    have hcardLen : q.1.support.toFinset.card = q.1.length + 1 := by
      rw [List.toFinset_card_of_nodup q.property.support_nodup,
        q.1.length_support]
    omega
  have hq4 : q.1.getVert 4 = s.right := by
    simpa [hqLen] using q.1.getVert_length
  have hadjQlast : (G.twoColorGraph (F.erase s.omitted) switched a c).Adj
      (q.1.getVert 3) s.right := by
    simpa [hq4] using q.1.adj_getVert_succ
      (i := 3) (by omega : 3 < q.1.length)
  obtain ⟨r, hrF, hr3, hrR, hrColor⟩ :=
    G.exists_twoColorWitnessEdge
      (F.erase s.omitted) switched a c hadjQlast
  have hrNeC : switched r ≠ c :=
    G.color_ne_of_mem_missingColorsAt
      (F.erase s.omitted) switched s.right c hc hrF hrR
  have hrA : switched r = a := hrColor.resolve_right hrNeC
  have hrg3 : r = g3 := by
    apply hproper s.right
    · exact Finset.mem_coe.mpr (Finset.mem_filter.mpr ⟨hrF, hrR⟩)
    · exact Finset.mem_coe.mpr (Finset.mem_filter.mpr ⟨hg3F, hg3R⟩)
    · exact hrA.trans hg3New.symm
  have hqOther := G.kempeOtherEndpoint_eq_of_incident
    hrR hr3 hadjQlast.ne.symm
  have hpOther := G.kempeOtherEndpoint_eq_of_incident
    hg3R hg3T hadjLast.ne.symm
  rw [hrg3] at hqOther
  have hq3t : q.1.getVert 3 = t := hqOther.symm.trans hpOther
  exact ⟨switched, hproper, ha, hc, q, hfive,
    by simpa [z] using hzOut, by simpa [t] using hq3t⟩

/-- In the separate-component case, the switched path can reenter the
original five vertices at its middle position only through one of the
first two internal vertices. -/
theorem FivePathState.second_switched_critical_path_vertex_case
    {F : Finset G.E} {k d : ℕ} {a b c : Fin k}
    (s : G.FivePathState F k a b)
    (hcritical : G.IsColorCriticalOn F k)
    (hdk : d + 1 < k) (hdegree : ∀ z, G.degreeOn F z ≤ d)
    (hthreshold : 7 * d < 6 * k + 2)
    (hleft : FivePathState.HasExternalColorAt G s c s.left)
    (hright : FivePathState.HasExternalColorAt G s c s.right)
    (hseparate :
      (G.twoColorGraph (F.erase s.omitted) s.paint b c).connectedComponentMk
          s.left ≠
        (G.twoColorGraph (F.erase s.omitted) s.paint b c).connectedComponentMk
          s.right) :
    ∃ switched : G.E → Fin k,
      ∃ q : (G.twoColorGraph (F.erase s.omitted) switched a c).Path
        s.left s.right,
        q.1.support.toFinset.card = 5 ∧
        q.1.getVert 1 ∉ s.path.1.support.toFinset ∧
        q.1.getVert 3 = s.path.1.getVert 3 ∧
        (q.1.getVert 2 ∉ s.path.1.support.toFinset ∨
          q.1.getVert 2 = s.path.1.getVert 1 ∨
          q.1.getVert 2 = s.path.1.getVert 2) := by
  obtain ⟨switched, _, _, _, q, hcard, hfirst, hthird⟩ :=
    FivePathState.first_switched_critical_path_vertex_outside G s
      hcritical hdk hdegree hthreshold hleft hright hseparate
  have hqLen : q.1.length = 4 := by
    have hcardLen : q.1.support.toFinset.card = q.1.length + 1 := by
      rw [List.toFinset_card_of_nodup q.property.support_nodup,
        q.1.length_support]
    omega
  have hq20 : q.1.getVert 2 ≠ s.left := by
    intro h
    have hidx := q.property.getVert_injOn
      (show 2 ∈ Set.Iic q.1.length by exact Set.mem_Iic.mpr (by omega))
      (show 0 ∈ Set.Iic q.1.length by exact Set.mem_Iic.mpr (by omega))
      (by simpa using h)
    omega
  have hq24 : q.1.getVert 2 ≠ s.right := by
    intro h
    have h4 : q.1.getVert 4 = s.right := by
      simpa [hqLen] using q.1.getVert_length
    have hidx := q.property.getVert_injOn
      (show 2 ∈ Set.Iic q.1.length by exact Set.mem_Iic.mpr (by omega))
      (show 4 ∈ Set.Iic q.1.length by exact Set.mem_Iic.mpr (by omega))
      (h.trans h4.symm)
    omega
  have hq23 : q.1.getVert 2 ≠ s.path.1.getVert 3 := by
    intro h
    have hidx := q.property.getVert_injOn
      (show 2 ∈ Set.Iic q.1.length by exact Set.mem_Iic.mpr (by omega))
      (show 3 ∈ Set.Iic q.1.length by exact Set.mem_Iic.mpr (by omega))
      (h.trans hthird.symm)
    omega
  refine ⟨switched, q, hcard, hfirst, hthird, ?_⟩
  by_cases hmiddle : q.1.getVert 2 ∈ s.path.1.support.toFinset
  · right
    obtain ⟨i, hi, hiLe⟩ :=
      SimpleGraph.Walk.mem_support_iff_exists_getVert.mp
        (by simpa using hmiddle : q.1.getVert 2 ∈ s.path.1.support)
    have hiLe' : i ≤ 4 := by
      have hlen := s.path_len
      omega
    interval_cases i
    · exact False.elim (hq20 (by simpa using hi.symm))
    · exact Or.inl (by simpa using hi.symm)
    · exact Or.inr (by simpa using hi.symm)
    · exact False.elim (hq23 (by simpa using hi.symm))
    · have hp4 : s.path.1.getVert 4 = s.right := by
        simpa [s.path_len] using s.path.1.getVert_length
      exact False.elim (hq24 (by simpa [hp4] using hi.symm))
  · exact Or.inl hmiddle

end WeightedEdgeColoring.WeightedMultigraph
