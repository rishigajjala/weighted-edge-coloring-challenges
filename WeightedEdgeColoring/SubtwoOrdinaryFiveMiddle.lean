import WeightedEdgeColoring.SubtwoOrdinaryFiveMirror

/-!
# Transporting five-chain saturation through an omitted-edge shift
-/

namespace WeightedEdgeColoring.WeightedMultigraph

universe u
variable (G : WeightedMultigraph.{u})

theorem pathEndpointsCast_getVert
    {H : SimpleGraph G.V} {x x' y y' : G.V}
    (hx : x' = x) (hy : y' = y) (p : H.Path x y) (i : ℕ) :
    (G.pathEndpointsCast hx hy p).1.getVert i = p.1.getVert i := by
  cases hx
  cases hy
  rfl

/-- The first internal vertex of an oriented critical path is saturated
even when the stored orientation of the omitted edge is unknown. -/
theorem first_internal_missingColor_edge_internal_of_incident_endpoints
    {F : Finset G.E} {k d : ℕ} (hcritical : G.IsColorCriticalOn F k)
    {e : G.E} (heF : e ∈ F) {color : G.E → Fin k}
    (hproper : G.IsProperOn (F.erase e) color)
    {a b : Fin k} {u v : G.V} (huv : u ≠ v)
    (heu : G.Inc u e) (hev : G.Inc v e)
    (ha : a ∈ G.missingColorsAt (F.erase e) color u)
    (hb : b ∈ G.missingColorsAt (F.erase e) color v)
    (q : (G.twoColorGraph (F.erase e) color a b).Path u v)
    (hqLen : q.1.length = 4)
    (hdk : d + 1 < k) (hdegree : ∀ z, G.degreeOn F z ≤ d)
    (hthreshold : 7 * d < 6 * k + 2)
    {g : G.E} (hgF : g ∈ F.erase e)
    (hg1 : G.Inc (q.1.getVert 1) g)
    (hgc : color g ∈ G.missingColorsAt (F.erase e) color v) :
    g ∈ G.internalEdges (F.erase e) q.1.support.toFinset := by
  have hends := G.endpoint_eq_or_endpoint_eq_swap_of_inc huv heu hev
  rcases hends with ⟨hfst, hsnd⟩ | ⟨hfst, hsnd⟩
  · let q' := G.pathEndpointsCast hfst hsnd q
    have hqLen' : q'.1.length = 4 := by
      rw [G.pathEndpointsCast_length]
      exact hqLen
    have hq1 : q'.1.getVert 1 = q.1.getVert 1 := by
      cases hfst; cases hsnd; rfl
    have hresult := G.first_internal_missingColor_edge_internal_fivePath
      hcritical heF hproper
      (by simpa [hfst] using ha)
      (by simpa [hsnd] using hb)
      q' hqLen' hdk hdegree hthreshold hgF (by simpa [hq1] using hg1)
      (Finset.mem_union.mpr (Or.inr (by simpa [hsnd] using hgc)))
    have hsupport : q'.1.support.toFinset = q.1.support.toFinset := by
      rw [G.pathEndpointsCast_support]
    rwa [hsupport] at hresult
  · have hswap := G.twoColorGraph_swap color b a (F := F.erase e)
    let qr := G.pathCast hswap q.reverse
    let q' := G.pathEndpointsCast hfst hsnd qr
    have hqLen' : q'.1.length = 4 := by
      rw [G.pathEndpointsCast_length, G.pathCast_length]
      simpa using hqLen
    have hqSupport : q'.1.support.toFinset = q.1.support.toFinset := by
      rw [G.pathEndpointsCast_support, G.pathCast_support]
      simp
    have hq3 : q'.1.getVert 3 = q.1.getVert 1 := by
      rw [G.pathEndpointsCast_getVert, G.pathCast_getVert]
      change q.1.reverse.getVert 3 = q.1.getVert 1
      rw [SimpleGraph.Walk.getVert_reverse, hqLen]
    have hresult := G.last_internal_missingColor_edge_internal_fivePath
      hcritical heF hproper
      (by simpa [hfst] using hb)
      (by simpa [hsnd] using ha)
      q' hqLen' hdk hdegree hthreshold hgF (by simpa [hq3] using hg1)
      (Finset.mem_union.mpr (Or.inl (by simpa [hfst] using hgc)))
    simpa [hqSupport] using hresult

/-- The first neighbor of an arbitrary oriented two-color path is fixed by
the unique edge of the second color at its first endpoint. -/
theorem first_neighbor_eq_of_colored_edge
    {F : Finset G.E} {k : ℕ} {color : G.E → Fin k}
    (hproper : G.IsProperOn F color)
    {a b : Fin k} {u v : G.V}
    (ha : a ∈ G.missingColorsAt F color u)
    (q : (G.twoColorGraph F color a b).Path u v)
    (hlen : 1 ≤ q.1.length)
    {g : G.E} (hgF : g ∈ F)
    {w : G.V} (huw : u ≠ w)
    (hgu : G.Inc u g) (hgw : G.Inc w g)
    (hgb : color g = b) : q.1.getVert 1 = w := by
  have hadj : (G.twoColorGraph F color a b).Adj
      u (q.1.getVert 1) := by
    simpa using q.1.adj_getVert_succ (i := 0) (by omega)
  obtain ⟨r, hrF, hru, hrz, hrcol⟩ :=
    G.exists_twoColorWitnessEdge F color a b hadj
  have hrneA : color r ≠ a :=
    G.color_ne_of_mem_missingColorsAt F color u a ha hrF hru
  have hrb : color r = b := hrcol.resolve_left hrneA
  have hrg : r = g := by
    apply hproper u
    · exact Finset.mem_coe.mpr (Finset.mem_filter.mpr ⟨hrF, hru⟩)
    · exact Finset.mem_coe.mpr (Finset.mem_filter.mpr ⟨hgF, hgu⟩)
    · exact hrb.trans hgb.symm
  have hqNe : u ≠ q.1.getVert 1 := hadj.ne
  have hotherQ := G.kempeOtherEndpoint_eq_of_incident hru hrz hqNe
  have hotherW := G.kempeOtherEndpoint_eq_of_incident hgu hgw huw
  rw [hrg] at hotherQ
  exact hotherQ.symm.trans hotherW

/-- After shifting the omitted edge to the last edge of a fixed five-chain,
the original middle vertex becomes its first internal vertex. Hence a color
missing at the original second endpoint cannot leave the five-chain there. -/
theorem middle_internal_secondMissingColor_edge_internal_fivePath
    {F : Finset G.E} {k d : ℕ} (hcritical : G.IsColorCriticalOn F k)
    {e : G.E} (heF : e ∈ F) {color : G.E → Fin k}
    (hproper : G.IsProperOn (F.erase e) color)
    {a b c : Fin k}
    (ha : a ∈ G.missingColorsAt (F.erase e) color (G.fst e))
    (hb : b ∈ G.missingColorsAt (F.erase e) color (G.snd e))
    (hc : c ∈ G.missingColorsAt (F.erase e) color (G.snd e))
    (p : (G.twoColorGraph (F.erase e) color a b).Path
      (G.fst e) (G.snd e)) (hpLen : p.1.length = 4)
    (hdk : d + 1 < k) (hdegree : ∀ z, G.degreeOn F z ≤ d)
    (hthreshold : 7 * d < 6 * k + 2)
    {r : G.E} (hrF : r ∈ F.erase e)
    (hrZ : G.Inc (p.1.getVert 2) r) (hrc : color r = c) :
    r ∈ G.internalEdges (F.erase e) p.1.support.toFinset := by
  obtain ⟨g, hgF, hgZ, hgY, hga, hproperNew, haNew, hbNew⟩ :=
    G.exists_proper_shift_to_last_edge_with_endpoint_palettes
      hcritical heF hproper ha hb p hpLen
  obtain ⟨q, hqLen, hqSupport⟩ :=
    G.exists_shifted_last_edge_fivePath
      hcritical heF hproper ha hb p hpLen hgF hgZ hga
  have hab : a ≠ b := G.critical_endpoint_missingColors_ne
    hcritical heF hproper ha hb
  have hac : a ≠ c := G.critical_endpoint_missingColors_ne
    hcritical heF hproper ha hc
  have hrg : r ≠ g := by
    intro heq
    exact hac (hga.symm.trans (heq ▸ hrc))
  have hrFg : r ∈ F.erase g :=
    Finset.mem_erase.mpr ⟨hrg, (Finset.mem_erase.mp hrF).2⟩
  have hcNew : c ∈ G.missingColorsAt (F.erase g)
      (G.assignEdgeColor color e a) (G.snd e) :=
    G.mem_missingColorsAt_shiftOmitted_of_ne hac.symm hc
  obtain ⟨g₂, hg₂F, hg₂2, hg₂3, hg₂b⟩ :=
    G.exists_third_criticalPath_edge_secondColor hproper hb p hpLen
  have hg₂g : g₂ ≠ g := by
    intro heq
    exact hab (hga.symm.trans (heq ▸ hg₂b))
  have hg₂Fg : g₂ ∈ F.erase g :=
    Finset.mem_erase.mpr ⟨hg₂g, (Finset.mem_erase.mp hg₂F).2⟩
  have hg₂New : G.assignEdgeColor color e a g₂ = b := by
    rw [G.assignEdgeColor_of_ne color (Finset.mem_erase.mp hg₂F).1 a]
    exact hg₂b
  have hZ3Z2 : p.1.getVert 3 ≠ p.1.getVert 2 :=
    (p.1.adj_getVert_succ (i := 2) (by omega)).ne.symm
  have hq1 : q.1.getVert 1 = p.1.getVert 2 :=
    G.first_neighbor_eq_of_colored_edge hproperNew haNew q (by omega)
      hg₂Fg hZ3Z2 hg₂3 hg₂2 hg₂New
  have hZ3Y : p.1.getVert 3 ≠ G.snd e := by
    have h := G.criticalPath_last_internal p (by omega)
    simpa [hpLen] using h.2.2
  have hrNew : G.assignEdgeColor color e a r = c := by
    rw [G.assignEdgeColor_of_ne color (Finset.mem_erase.mp hrF).1 a]
    exact hrc
  have hnew := G.first_internal_missingColor_edge_internal_of_incident_endpoints
    hcritical (Finset.mem_erase.mp hgF).2 hproperNew hZ3Y hgZ hgY
    haNew hbNew q hqLen hdk hdegree hthreshold hrFg
    (by simpa [hq1] using hrZ)
    (by rw [hrNew]; exact hcNew)
  have hdata := Finset.mem_filter.mp hnew
  have hsupport : r ∈ G.internalEdges (F.erase g) p.1.support.toFinset := by
    rwa [hqSupport] at hnew
  exact Finset.mem_filter.mpr ⟨hrF, (Finset.mem_filter.mp hsupport).2⟩

/-- The corresponding middle-vertex statement for a color missing at the
first endpoint follows by reversing all stored edge orientations. -/
theorem middle_internal_firstMissingColor_edge_internal_fivePath
    {F : Finset G.E} {k d : ℕ} (hcritical : G.IsColorCriticalOn F k)
    {e : G.E} (heF : e ∈ F) {color : G.E → Fin k}
    (hproper : G.IsProperOn (F.erase e) color)
    {a b c : Fin k}
    (ha : a ∈ G.missingColorsAt (F.erase e) color (G.fst e))
    (hb : b ∈ G.missingColorsAt (F.erase e) color (G.snd e))
    (hc : c ∈ G.missingColorsAt (F.erase e) color (G.fst e))
    (p : (G.twoColorGraph (F.erase e) color a b).Path
      (G.fst e) (G.snd e)) (hpLen : p.1.length = 4)
    (hdk : d + 1 < k) (hdegree : ∀ z, G.degreeOn F z ≤ d)
    (hthreshold : 7 * d < 6 * k + 2)
    {r : G.E} (hrF : r ∈ F.erase e)
    (hrZ : G.Inc (p.1.getVert 2) r) (hrc : color r = c) :
    r ∈ G.internalEdges (F.erase e) p.1.support.toFinset := by
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
  have hq2 : q.1.getVert 2 = p.1.getVert 2 := by
    rw [G.pathCast_getVert]
    change p.1.reverse.getVert 2 = p.1.getVert 2
    rw [SimpleGraph.Walk.getVert_reverse, hpLen]
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
  have hcR : c ∈ R.missingColorsAt (F.erase e) color (R.snd e) := by
    simpa [R] using hc
  have hrZR : R.Inc (q.1.getVert 2) r := by
    simpa [R, hq2] using hrZ
  have hresult := R.middle_internal_secondMissingColor_edge_internal_fivePath
    hcriticalR heF hproperR hbR haR hcR q hqLen hdk hdegreeR
    hthreshold hrF hrZR hrc
  simpa [R, hqSupport] using hresult

/-- Every edge at the middle vertex whose color is missing at one of the
original endpoints stays within the fixed critical five-chain. -/
theorem middle_internal_missingColor_edge_internal_fivePath
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
    {r : G.E} (hrF : r ∈ F.erase e)
    (hrZ : G.Inc (p.1.getVert 2) r)
    (hrMissing : color r ∈
      G.missingColorsAt (F.erase e) color (G.fst e) ∪
      G.missingColorsAt (F.erase e) color (G.snd e)) :
    r ∈ G.internalEdges (F.erase e) p.1.support.toFinset := by
  rcases Finset.mem_union.mp hrMissing with hcX | hcY
  · exact G.middle_internal_firstMissingColor_edge_internal_fivePath
      hcritical heF hproper ha hb hcX p hpLen hdk hdegree hthreshold
      hrF hrZ rfl
  · exact G.middle_internal_secondMissingColor_edge_internal_fivePath
      hcritical heF hproper ha hb hcY p hpLen hdk hdegree hthreshold
      hrF hrZ rfl

/-- Every edge at an internal path vertex in a color missing at either
endpoint stays within the fixed critical five-chain. -/
theorem internal_vertex_missingColor_edge_internal_fivePath
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
    {z : G.V} (hz : z ∈ p.1.support)
    (hzX : z ≠ G.fst e) (hzY : z ≠ G.snd e)
    {g : G.E} (hgF : g ∈ F.erase e) (hgz : G.Inc z g)
    (hgc : color g ∈
      G.missingColorsAt (F.erase e) color (G.fst e) ∪
      G.missingColorsAt (F.erase e) color (G.snd e)) :
    g ∈ G.internalEdges (F.erase e) p.1.support.toFinset := by
  obtain ⟨i, hi, hiLe⟩ :=
    SimpleGraph.Walk.mem_support_iff_exists_getVert.mp hz
  have hiLe' : i ≤ 4 := by omega
  interval_cases i
  · exact False.elim (hzX (by simpa using hi.symm))
  · exact G.first_internal_missingColor_edge_internal_fivePath
      hcritical heF hproper ha hb p hpLen hdk hdegree hthreshold
      hgF (by simpa [hi] using hgz) hgc
  · exact G.middle_internal_missingColor_edge_internal_fivePath
      hcritical heF hproper ha hb p hpLen hdk hdegree hthreshold
      hgF (by simpa [hi] using hgz) hgc
  · exact G.last_internal_missingColor_edge_internal_fivePath
      hcritical heF hproper ha hb p hpLen hdk hdegree hthreshold
      hgF (by simpa [hi] using hgz) hgc
  · have hp4 : p.1.getVert 4 = G.snd e := by
      simpa [hpLen] using p.1.getVert_length
    exact False.elim (hzY (by simpa [hp4] using hi.symm))

/-- Andersen's five-vertex chain-containment conclusion: once one
critical endpoint chain has five vertices, every other critical endpoint
chain in the same edge-deleted coloring uses only those five vertices. -/
theorem criticalPath_support_subset_fivePath
    {F : Finset G.E} {k d : ℕ} (hcritical : G.IsColorCriticalOn F k)
    {e : G.E} (heF : e ∈ F) {color : G.E → Fin k}
    (hproper : G.IsProperOn (F.erase e) color)
    {a b c f : Fin k}
    (ha : a ∈ G.missingColorsAt (F.erase e) color (G.fst e))
    (hb : b ∈ G.missingColorsAt (F.erase e) color (G.snd e))
    (hc : c ∈ G.missingColorsAt (F.erase e) color (G.fst e))
    (hf : f ∈ G.missingColorsAt (F.erase e) color (G.snd e))
    (p : (G.twoColorGraph (F.erase e) color a b).Path
      (G.fst e) (G.snd e)) (hpLen : p.1.length = 4)
    (q : (G.twoColorGraph (F.erase e) color c f).Path
      (G.fst e) (G.snd e))
    (hdk : d + 1 < k) (hdegree : ∀ z, G.degreeOn F z ≤ d)
    (hthreshold : 7 * d < 6 * k + 2) :
    q.1.support.toFinset ⊆ p.1.support.toFinset := by
  intro w hwq
  by_contra hwout
  have hwqList : w ∈ q.1.support := by simpa using hwq
  have hwoutList : w ∉ p.1.support := by simpa using hwout
  obtain ⟨hqLen, hwMiddle, hqFirstInP, _⟩ :=
    G.outside_criticalPath_vertex_is_middle_of_fivePath
      hcritical heF hproper ha hb hc hf p hpLen q hdk hdegree hthreshold
      hwqList hwoutList
  have hqFirst := G.criticalPath_first_internal q (by omega)
  obtain ⟨g, hgF, hg1, hg2, hgc⟩ :=
    G.exists_second_criticalPath_edge_firstColor hproper hc q (by omega)
  have hginternal := G.internal_vertex_missingColor_edge_internal_fivePath
    hcritical heF hproper ha hb p hpLen hdk hdegree hthreshold
    hqFirstInP hqFirst.2.1 hqFirst.2.2 hgF hg1
    (Finset.mem_union.mpr (Or.inl (hgc ▸ hc)))
  have hdata := (Finset.mem_filter.mp hginternal).2
  rcases (show G.Inc w g from hwMiddle ▸ hg2) with hfst | hsnd
  · exact hwout (by simpa [← hfst] using hdata.1)
  · exact hwout (by simpa [← hsnd] using hdata.2)

/-- Andersen Theorem 5(i): the combined critical neighborhood is exactly
the fixed five-vertex critical chain. -/
theorem criticalNeighborhood_eq_fivePath
    {F : Finset G.E} {k d : ℕ} (hcritical : G.IsColorCriticalOn F k)
    {e : G.E} (heF : e ∈ F) {color : G.E → Fin k}
    (hproper : G.IsProperOn (F.erase e) color)
    {a b : Fin k}
    (ha : a ∈ G.missingColorsAt (F.erase e) color (G.fst e))
    (hb : b ∈ G.missingColorsAt (F.erase e) color (G.snd e))
    (p : (G.twoColorGraph (F.erase e) color a b).Path
      (G.fst e) (G.snd e)) (hpLen : p.1.length = 4)
    (hdk : d + 1 < k) (hdegree : ∀ z, G.degreeOn F z ≤ d)
    (hthreshold : 7 * d < 6 * k + 2) :
    G.criticalNeighborhood (F := F) e color = p.1.support.toFinset := by
  apply Finset.Subset.antisymm
  · intro z hz
    rw [G.mem_criticalNeighborhood_iff] at hz
    rcases hz with ⟨c, f, hc, hf, q, hzq⟩ | hfanX | hfanY
    · exact G.criticalPath_support_subset_fivePath
        hcritical heF hproper ha hb hc hf p hpLen q hdk hdegree
        hthreshold (by simpa using hzq)
    · simpa using G.first_oneStepFan_subset_fivePath
        hcritical heF hproper ha hb p hpLen hdk hdegree hthreshold hfanX
    · simpa using G.second_oneStepFan_subset_fivePath
        hcritical heF hproper ha hb p hpLen hdk hdegree hthreshold hfanY
  · intro z hz
    rw [G.mem_criticalNeighborhood_iff]
    exact Or.inl ⟨a, b, ha, hb, p, by simpa using hz⟩

end WeightedEdgeColoring.WeightedMultigraph
