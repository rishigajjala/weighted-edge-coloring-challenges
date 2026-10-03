import WeightedEdgeColoring.SubtwoOrdinaryFiveMiddle

/-!
# Endpoint-missing colors on a saturated five-chain
-/

namespace WeightedEdgeColoring.WeightedMultigraph

universe u
variable (G : WeightedMultigraph.{u})

/-- Any edge incident to the five-chain whose color is missing at one of
the omitted edge's endpoints remains inside the five-chain. -/
theorem endpointMissingColor_edge_incident_fivePath_internal
    {F : Finset G.E} {k d : ℕ} (hcritical : G.IsColorCriticalOn F k)
    {e : G.E} (heF : e ∈ F) {color : G.E → Fin k}
    (hproper : G.IsProperOn (F.erase e) color)
    {a b : Fin k}
    (ha : a ∈ G.missingColorsAt (F.erase e) color (G.fst e))
    (hb : b ∈ G.missingColorsAt (F.erase e) color (G.snd e))
    (p : (G.twoColorGraph (F.erase e) color a b).Path
      (G.fst e) (G.snd e)) (hpLen : p.1.length = 4)
    (hdk : d + 1 < k) (hdegree : ∀ z, G.degreeOn F z ≤ d)
    (hthreshold : 7 * d < 6 * k + 2)
    {v : G.V} (hv : v ∈ p.1.support)
    {g : G.E} (hgF : g ∈ F.erase e) (hgv : G.Inc v g)
    (hgc : color g ∈
      G.missingColorsAt (F.erase e) color (G.fst e) ∪
      G.missingColorsAt (F.erase e) color (G.snd e)) :
    g ∈ G.internalEdges (F.erase e) p.1.support.toFinset := by
  by_cases hvX : v = G.fst e
  · subst v
    have hother (w : G.V) (hwout : w ∉ p.1.support)
        (hgw : G.Inc w g) : False := by
      rcases Finset.mem_union.mp hgc with hcX | hcY
      · exact (G.color_ne_of_mem_missingColorsAt
          (F.erase e) color (G.fst e) (color g) hcX hgF hgv) rfl
      · exact (G.outside_fivePath_no_endpoint_fanEdge
          hcritical heF hproper ha hb p hpLen hdk hdegree hthreshold
          hwout).1 ⟨g, hgF, hgv, hgw, hcY⟩
    apply Finset.mem_filter.mpr
    refine ⟨hgF, ?_⟩
    constructor
    · by_contra hfst
      exact hother (G.fst g) (by simpa using hfst) (Or.inl rfl)
    · by_contra hsnd
      exact hother (G.snd g) (by simpa using hsnd) (Or.inr rfl)
  by_cases hvY : v = G.snd e
  · subst v
    have hother (w : G.V) (hwout : w ∉ p.1.support)
        (hgw : G.Inc w g) : False := by
      rcases Finset.mem_union.mp hgc with hcX | hcY
      · exact (G.outside_fivePath_no_endpoint_fanEdge
          hcritical heF hproper ha hb p hpLen hdk hdegree hthreshold
          hwout).2 ⟨g, hgF, hgv, hgw, hcX⟩
      · exact (G.color_ne_of_mem_missingColorsAt
          (F.erase e) color (G.snd e) (color g) hcY hgF hgv) rfl
    apply Finset.mem_filter.mpr
    refine ⟨hgF, ?_⟩
    constructor
    · by_contra hfst
      exact hother (G.fst g) (by simpa using hfst) (Or.inl rfl)
    · by_contra hsnd
      exact hother (G.snd g) (by simpa using hsnd) (Or.inr rfl)
  exact G.internal_vertex_missingColor_edge_internal_fivePath
    hcritical heF hproper ha hb p hpLen hdk hdegree hthreshold
    hv hvX hvY hgF hgv hgc

theorem exists_edge_of_not_missingColor
    {F : Finset G.E} {k : ℕ} {color : G.E → Fin k}
    {v : G.V} {c : Fin k}
    (hc : c ∉ G.missingColorsAt F color v) :
    ∃ g, g ∈ F ∧ G.Inc v g ∧ color g = c := by
  classical
  have hused : c ∈ (F.filter (G.Inc v)).image color := by
    by_contra hnot
    exact hc (Finset.mem_sdiff.mpr ⟨Finset.mem_univ _, hnot⟩)
  obtain ⟨g, hg, hgc⟩ := Finset.mem_image.mp hused
  have hgData := Finset.mem_filter.mp hg
  exact ⟨g, hgData.1, hgData.2, hgc⟩

theorem false_of_three_distinct_vertices_incident_edge
    {u v w : G.V} (huv : u ≠ v) (huw : u ≠ w)
    (hvw : v ≠ w) {g : G.E}
    (hgu : G.Inc u g) (hgv : G.Inc v g) (hgw : G.Inc w g) : False := by
  rcases G.endpoint_eq_or_endpoint_eq_swap_of_inc huv hgu hgv with
    ⟨hfst, hsnd⟩ | ⟨hfst, hsnd⟩
  · rcases hgw with hw | hw
    · exact huw (hfst.symm.trans hw)
    · exact hvw (hsnd.symm.trans hw)
  · rcases hgw with hw | hw
    · exact hvw (hfst.symm.trans hw)
    · exact huw (hsnd.symm.trans hw)

/-- A color missing at the first omitted-edge endpoint already occurs on
two distinct edges internal to the critical five-chain. -/
theorem two_internal_edges_of_missing_first_fivePath
    {F : Finset G.E} {k d : ℕ} (hcritical : G.IsColorCriticalOn F k)
    {e : G.E} (heF : e ∈ F) {color : G.E → Fin k}
    (hproper : G.IsProperOn (F.erase e) color)
    {a b : Fin k}
    (ha : a ∈ G.missingColorsAt (F.erase e) color (G.fst e))
    (hb : b ∈ G.missingColorsAt (F.erase e) color (G.snd e))
    (p : (G.twoColorGraph (F.erase e) color a b).Path
      (G.fst e) (G.snd e)) (hpLen : p.1.length = 4)
    (hdk : d + 1 < k) (hdegree : ∀ z, G.degreeOn F z ≤ d)
    (hthreshold : 7 * d < 6 * k + 2)
    {c : Fin k}
    (hc : c ∈ G.missingColorsAt (F.erase e) color (G.fst e)) :
    ∃ g h, g ≠ h ∧
      g ∈ G.internalEdges (F.erase e) p.1.support.toFinset ∧
      h ∈ G.internalEdges (F.erase e) p.1.support.toFinset ∧
      color g = c ∧ color h = c := by
  have hdegreeErase : ∀ z, G.degreeOn (F.erase e) z + 2 ≤ k := by
    intro z
    have hz := (G.degreeOn_mono_critical (Finset.erase_subset e F) z).trans
      (hdegree z)
    omega
  have hpair := G.criticalNeighborhood_pairwise_disjoint_missingColorsAt
    hcritical heF hproper hdegreeErase
  have hD := G.criticalNeighborhood_eq_fivePath
    hcritical heF hproper ha hb p hpLen hdk hdegree hthreshold
  have hxD : G.fst e ∈ G.criticalNeighborhood (F := F) e color := by
    rw [hD]
    simpa using p.1.start_mem_support
  have hnot (v : G.V) (hv : v ∈ p.1.support)
      (hvX : v ≠ G.fst e) :
      c ∉ G.missingColorsAt (F.erase e) color v := by
    have hvD : v ∈ G.criticalNeighborhood (F := F) e color := by
      rw [hD]
      simpa using hv
    have hd := hpair hxD hvD hvX.symm
    exact (Finset.disjoint_left.mp hd hc)
  let y := G.snd e
  let z₁ := p.1.getVert 1
  let z₂ := p.1.getVert 2
  have hy : y ∈ p.1.support := p.1.end_mem_support
  have hz₁ : z₁ ∈ p.1.support := p.1.getVert_mem_support 1
  have hz₂ : z₂ ∈ p.1.support := p.1.getVert_mem_support 2
  have hxy : G.fst e ≠ y := G.noLoop e
  have hx1 : G.fst e ≠ z₁ := by
    have hadj := p.1.adj_getVert_succ (i := 0) (by omega)
    simpa [z₁] using hadj.ne
  have hx2 : G.fst e ≠ z₂ := by
    intro h
    have hi := p.property.getVert_injOn
      (show 0 ∈ Set.Iic p.1.length by simp)
      (show 2 ∈ Set.Iic p.1.length by simp [hpLen])
      (by simpa [z₂] using h)
    omega
  have hy1 : y ≠ z₁ := by
    intro h
    have hp4 : p.1.getVert 4 = y := by
      simpa [y, hpLen] using p.1.getVert_length
    have hi := p.property.getVert_injOn
      (show 4 ∈ Set.Iic p.1.length by simp [hpLen])
      (show 1 ∈ Set.Iic p.1.length by simp [hpLen])
      (hp4.trans h)
    omega
  have hy2 : y ≠ z₂ := by
    intro h
    have hp4 : p.1.getVert 4 = y := by
      simpa [y, hpLen] using p.1.getVert_length
    have hi := p.property.getVert_injOn
      (show 4 ∈ Set.Iic p.1.length by simp [hpLen])
      (show 2 ∈ Set.Iic p.1.length by simp [hpLen])
      (hp4.trans h)
    omega
  have h12 : z₁ ≠ z₂ :=
    (p.1.adj_getVert_succ (i := 1) (by omega)).ne
  obtain ⟨gY, hgYF, hgYY, hgYc⟩ :=
    G.exists_edge_of_not_missingColor (hnot y hy hxy.symm)
  obtain ⟨g1, hg1F, hg11, hg1c⟩ :=
    G.exists_edge_of_not_missingColor (hnot z₁ hz₁ hx1.symm)
  obtain ⟨g2, hg2F, hg22, hg2c⟩ :=
    G.exists_edge_of_not_missingColor (hnot z₂ hz₂ hx2.symm)
  have hgYInternal := G.endpointMissingColor_edge_incident_fivePath_internal
    hcritical heF hproper ha hb p hpLen hdk hdegree hthreshold
    hy hgYF hgYY (Finset.mem_union.mpr (Or.inl (hgYc ▸ hc)))
  have hg1Internal := G.endpointMissingColor_edge_incident_fivePath_internal
    hcritical heF hproper ha hb p hpLen hdk hdegree hthreshold
    hz₁ hg1F hg11 (Finset.mem_union.mpr (Or.inl (hg1c ▸ hc)))
  have hg2Internal := G.endpointMissingColor_edge_incident_fivePath_internal
    hcritical heF hproper ha hb p hpLen hdk hdegree hthreshold
    hz₂ hg2F hg22 (Finset.mem_union.mpr (Or.inl (hg2c ▸ hc)))
  by_cases hY1 : gY ≠ g1
  · exact ⟨gY, g1, hY1, hgYInternal, hg1Internal, hgYc, hg1c⟩
  · have hY2 : gY ≠ g2 := by
      intro heq
      have heqY1 : gY = g1 := by
        by_contra hne
        exact hY1 hne
      exact G.false_of_three_distinct_vertices_incident_edge
        hy1 hy2 h12 hgYY (heqY1.symm ▸ hg11) (heq.symm ▸ hg22)
    exact ⟨gY, g2, hY2, hgYInternal, hg2Internal, hgYc, hg2c⟩

/-- The symmetric two-edge conclusion for a color missing at the second
omitted-edge endpoint. -/
theorem two_internal_edges_of_missing_second_fivePath
    {F : Finset G.E} {k d : ℕ} (hcritical : G.IsColorCriticalOn F k)
    {e : G.E} (heF : e ∈ F) {color : G.E → Fin k}
    (hproper : G.IsProperOn (F.erase e) color)
    {a b : Fin k}
    (ha : a ∈ G.missingColorsAt (F.erase e) color (G.fst e))
    (hb : b ∈ G.missingColorsAt (F.erase e) color (G.snd e))
    (p : (G.twoColorGraph (F.erase e) color a b).Path
      (G.fst e) (G.snd e)) (hpLen : p.1.length = 4)
    (hdk : d + 1 < k) (hdegree : ∀ z, G.degreeOn F z ≤ d)
    (hthreshold : 7 * d < 6 * k + 2)
    {c : Fin k}
    (hc : c ∈ G.missingColorsAt (F.erase e) color (G.snd e)) :
    ∃ g h, g ≠ h ∧
      g ∈ G.internalEdges (F.erase e) p.1.support.toFinset ∧
      h ∈ G.internalEdges (F.erase e) p.1.support.toFinset ∧
      color g = c ∧ color h = c := by
  let R := G.reverseEndpoints
  have hgraph : R.twoColorGraph (F.erase e) color b a =
      G.twoColorGraph (F.erase e) color a b :=
    G.reverseEndpoints_twoColorGraph color a b
  let q : (R.twoColorGraph (F.erase e) color b a).Path
      (R.fst e) (R.snd e) := G.pathCast hgraph p.reverse
  have hqLen : q.1.length = 4 := by
    rw [G.pathCast_length]
    simpa using hpLen
  have hqSupport : q.1.support.toFinset = p.1.support.toFinset := by
    rw [G.pathCast_support]
    simp
  have hproperR : R.IsProperOn (F.erase e) color :=
    G.reverseEndpoints_proper_iff.mpr hproper
  have hcriticalR : R.IsColorCriticalOn F k :=
    G.reverseEndpoints_critical_iff.mpr hcritical
  have hdegreeR : ∀ z, R.degreeOn F z ≤ d := by
    intro z
    simpa [R] using hdegree z
  have hbR : b ∈ R.missingColorsAt (F.erase e) color (R.fst e) := by
    simpa [R] using hb
  have haR : a ∈ R.missingColorsAt (F.erase e) color (R.snd e) := by
    simpa [R] using ha
  have hcR : c ∈ R.missingColorsAt (F.erase e) color (R.fst e) := by
    simpa [R] using hc
  obtain ⟨g, h, hne, hg, hh, hgc, hhc⟩ :=
    R.two_internal_edges_of_missing_first_fivePath
      hcriticalR heF hproperR hbR haR q hqLen hdk hdegreeR
      hthreshold hcR
  exact ⟨g, h, hne, by simpa [R, hqSupport] using hg,
    by simpa [R, hqSupport] using hh, hgc, hhc⟩

theorem two_internal_edges_of_missing_endpoint_fivePath
    {F : Finset G.E} {k d : ℕ} (hcritical : G.IsColorCriticalOn F k)
    {e : G.E} (heF : e ∈ F) {color : G.E → Fin k}
    (hproper : G.IsProperOn (F.erase e) color)
    {a b : Fin k}
    (ha : a ∈ G.missingColorsAt (F.erase e) color (G.fst e))
    (hb : b ∈ G.missingColorsAt (F.erase e) color (G.snd e))
    (p : (G.twoColorGraph (F.erase e) color a b).Path
      (G.fst e) (G.snd e)) (hpLen : p.1.length = 4)
    (hdk : d + 1 < k) (hdegree : ∀ z, G.degreeOn F z ≤ d)
    (hthreshold : 7 * d < 6 * k + 2)
    {c : Fin k}
    (hc : c ∈ G.missingColorsAt (F.erase e) color (G.fst e) ∪
      G.missingColorsAt (F.erase e) color (G.snd e)) :
    ∃ g h, g ≠ h ∧
      g ∈ G.internalEdges (F.erase e) p.1.support.toFinset ∧
      h ∈ G.internalEdges (F.erase e) p.1.support.toFinset ∧
      color g = c ∧ color h = c := by
  rcases Finset.mem_union.mp hc with hcX | hcY
  · exact G.two_internal_edges_of_missing_first_fivePath
      hcritical heF hproper ha hb p hpLen hdk hdegree hthreshold hcX
  · exact G.two_internal_edges_of_missing_second_fivePath
      hcritical heF hproper ha hb p hpLen hdk hdegree hthreshold hcY

end WeightedEdgeColoring.WeightedMultigraph
