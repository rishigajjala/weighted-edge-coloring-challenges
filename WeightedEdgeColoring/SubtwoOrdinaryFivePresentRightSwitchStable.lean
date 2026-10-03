import WeightedEdgeColoring.SubtwoOrdinaryFivePresentRightComponentZ3

namespace WeightedEdgeColoring.WeightedMultigraph

universe u
variable (G : WeightedMultigraph.{u})

theorem FivePathState.first_switched_critical_path_vertex_outside_with_stability
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
      (∀ g, s.paint g ≠ b → s.paint g ≠ c →
        switched g = s.paint g) ∧
      (∀ v, (G.twoColorGraph (F.erase s.omitted) s.paint b c).connectedComponentMk
          v ≠
        (G.twoColorGraph (F.erase s.omitted) s.paint b c).connectedComponentMk
          s.right →
        ∀ g ∈ F.erase s.omitted, G.Inc v g →
          switched g = s.paint g) ∧
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
  obtain ⟨switched, hproper, ha, hc, hother, hstable, hleftStable, q, hcard⟩ :=
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
  exact ⟨switched, hproper, ha, hc, hother, hstable, q, hfive,
    by simpa [z] using hzOut, by simpa [t] using hq3t⟩

end WeightedEdgeColoring.WeightedMultigraph
