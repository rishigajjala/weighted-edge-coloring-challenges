import WeightedEdgeColoring.SubtwoOrdinaryFiveInnerColors

/-!
# The middle-vertex missing-color case
-/

namespace WeightedEdgeColoring.WeightedMultigraph

universe u
variable (G : WeightedMultigraph.{u})

theorem two_internal_edges_of_missing_at_first_internal_incident_endpoints
    {F : Finset G.E} {k d : ℕ} (hcritical : G.IsColorCriticalOn F k)
    {e : G.E} (heF : e ∈ F) {color : G.E → Fin k}
    (hproper : G.IsProperOn (F.erase e) color)
    {a b c : Fin k} {u v : G.V} (huv : u ≠ v)
    (heu : G.Inc u e) (hev : G.Inc v e)
    (ha : a ∈ G.missingColorsAt (F.erase e) color u)
    (hb : b ∈ G.missingColorsAt (F.erase e) color v)
    (q : (G.twoColorGraph (F.erase e) color a b).Path u v)
    (hqLen : q.1.length = 4)
    (hdk : d + 1 < k) (hdegree : ∀ z, G.degreeOn F z ≤ d)
    (hthreshold : 7 * d < 6 * k + 2)
    (hc : c ∈ G.missingColorsAt (F.erase e) color (q.1.getVert 1)) :
    ∃ r s, r ≠ s ∧
      r ∈ G.internalEdges (F.erase e) q.1.support.toFinset ∧
      s ∈ G.internalEdges (F.erase e) q.1.support.toFinset ∧
      color r = c ∧ color s = c := by
  have hends := G.endpoint_eq_or_endpoint_eq_swap_of_inc huv heu hev
  rcases hends with ⟨hfst, hsnd⟩ | ⟨hfst, hsnd⟩
  · let q' := G.pathEndpointsCast hfst hsnd q
    have hqLen' : q'.1.length = 4 := by
      rw [G.pathEndpointsCast_length]
      exact hqLen
    have hq1 : q'.1.getVert 1 = q.1.getVert 1 :=
      G.pathEndpointsCast_getVert hfst hsnd q 1
    obtain ⟨r,s,hrs,hr,hs,hrc,hsc⟩ :=
      G.two_internal_edges_of_missing_first_internal_fivePath
        hcritical heF hproper (by simpa [hfst] using ha)
        (by simpa [hsnd] using hb) q' hqLen' hdk hdegree hthreshold
        (by simpa [hq1] using hc)
    have hsupport : q'.1.support.toFinset = q.1.support.toFinset := by
      rw [G.pathEndpointsCast_support]
    exact ⟨r,s,hrs, by simpa [hsupport] using hr,
      by simpa [hsupport] using hs,hrc,hsc⟩
  · have hswap := G.twoColorGraph_swap color b a (F := F.erase e)
    let qr := G.pathCast hswap q.reverse
    let q' := G.pathEndpointsCast hfst hsnd qr
    have hqLen' : q'.1.length = 4 := by
      rw [G.pathEndpointsCast_length, G.pathCast_length]
      simpa using hqLen
    have hsupport : q'.1.support.toFinset = q.1.support.toFinset := by
      rw [G.pathEndpointsCast_support, G.pathCast_support]
      simp
    have hq3 : q'.1.getVert 3 = q.1.getVert 1 := by
      rw [G.pathEndpointsCast_getVert, G.pathCast_getVert]
      change q.1.reverse.getVert 3 = q.1.getVert 1
      rw [SimpleGraph.Walk.getVert_reverse, hqLen]
    obtain ⟨r,s,hrs,hr,hs,hrc,hsc⟩ :=
      G.two_internal_edges_of_missing_third_fivePath
        hcritical heF hproper (by simpa [hfst] using hb)
        (by simpa [hsnd] using ha) q' hqLen' hdk hdegree hthreshold
        (by simpa [hq3] using hc)
    exact ⟨r,s,hrs, by simpa [hsupport] using hr,
      by simpa [hsupport] using hs,hrc,hsc⟩

/-- A color missing at the middle vertex occurs on two distinct internal
edges of the original five-chain. The first shift makes that vertex the
first internal vertex, and the previous theorem performs the second shift. -/
theorem two_internal_edges_of_missing_middle_fivePath
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
    (hc : c ∈ G.missingColorsAt (F.erase e) color (p.1.getVert 2)) :
    ∃ r s, r ≠ s ∧
      r ∈ G.internalEdges (F.erase e) p.1.support.toFinset ∧
      s ∈ G.internalEdges (F.erase e) p.1.support.toFinset ∧
      color r = c ∧ color s = c := by
  obtain ⟨g, hgF, hgZ, hgY, hga, hproperNew, haNew, hbNew⟩ :=
    G.exists_proper_shift_to_last_edge_with_endpoint_palettes
      hcritical heF hproper ha hb p hpLen
  obtain ⟨q, hqLen, hqSupport⟩ :=
    G.exists_shifted_last_edge_fivePath
      hcritical heF hproper ha hb p hpLen hgF hgZ hga
  obtain ⟨g₁, hg₁F, hg₁1, hg₁2, hg₁a⟩ :=
    G.exists_second_criticalPath_edge_firstColor hproper ha p (by omega)
  have hca : c ≠ a := by
    intro heq
    have hne := G.color_ne_of_mem_missingColorsAt
      (F.erase e) color (p.1.getVert 2) c hc hg₁F hg₁2
    exact hne (hg₁a.trans heq.symm)
  have hcNew : c ∈ G.missingColorsAt (F.erase g)
      (G.assignEdgeColor color e a) (p.1.getVert 2) :=
    G.mem_missingColorsAt_shiftOmitted_of_ne hca hc
  obtain ⟨g₂, hg₂F, hg₂2, hg₂3, hg₂b⟩ :=
    G.exists_third_criticalPath_edge_secondColor hproper hb p hpLen
  have hab : a ≠ b := G.critical_endpoint_missingColors_ne
    hcritical heF hproper ha hb
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
  have hcQ : c ∈ G.missingColorsAt (F.erase g)
      (G.assignEdgeColor color e a) (q.1.getVert 1) := by
    rw [hq1]
    exact hcNew
  have hZ3Y : p.1.getVert 3 ≠ G.snd e := by
    have h := G.criticalPath_last_internal p (by omega)
    simpa [hpLen] using h.2.2
  obtain ⟨r,s,hrs,hr,hs,hrc,hsc⟩ :=
    G.two_internal_edges_of_missing_at_first_internal_incident_endpoints
      hcritical (Finset.mem_erase.mp hgF).2 hproperNew hZ3Y hgZ hgY
      haNew hbNew q hqLen hdk hdegree hthreshold hcQ
  have htransfer (t : G.E)
      (ht : t ∈ G.internalEdges (F.erase g) q.1.support.toFinset)
      (htc : G.assignEdgeColor color e a t = c) :
      t ∈ G.internalEdges (F.erase e) p.1.support.toFinset ∧
        color t = c := by
    have htData := Finset.mem_filter.mp ht
    have hte : t ≠ e := by
      intro heq
      have hac : a = c := by simpa [heq] using htc
      exact hca hac.symm
    have htF : t ∈ F.erase e :=
      Finset.mem_erase.mpr ⟨hte, (Finset.mem_erase.mp htData.1).2⟩
    have htOld : color t = c := by
      simpa [G.assignEdgeColor_of_ne color hte a] using htc
    refine ⟨Finset.mem_filter.mpr ⟨htF, ?_⟩, htOld⟩
    simpa [hqSupport] using htData.2
  obtain ⟨hrOld, hrcOld⟩ := htransfer r hr hrc
  obtain ⟨hsOld, hscOld⟩ := htransfer s hs hsc
  exact ⟨r,s,hrs,hrOld,hsOld,hrcOld,hscOld⟩

/-- Andersen Theorem 5(ii): every color missing at any vertex of a
five-vertex critical chain occurs on two distinct internal edges. -/
theorem two_internal_edges_of_missing_some_fivePath
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
    {c : Fin k} {v : G.V}
    (hv : v ∈ p.1.support)
    (hc : c ∈ G.missingColorsAt (F.erase e) color v) :
    ∃ r s, r ≠ s ∧
      r ∈ G.internalEdges (F.erase e) p.1.support.toFinset ∧
      s ∈ G.internalEdges (F.erase e) p.1.support.toFinset ∧
      color r = c ∧ color s = c := by
  obtain ⟨i, hi, hiLe⟩ :=
    SimpleGraph.Walk.mem_support_iff_exists_getVert.mp hv
  have hiLe' : i ≤ 4 := by omega
  interval_cases i
  · have hvX : v = G.fst e := by simpa using hi.symm
    exact G.two_internal_edges_of_missing_first_fivePath
      hcritical heF hproper ha hb p hpLen hdk hdegree hthreshold
      (by simpa [hvX] using hc)
  · exact G.two_internal_edges_of_missing_first_internal_fivePath
      hcritical heF hproper ha hb p hpLen hdk hdegree hthreshold
      (by simpa [hi] using hc)
  · exact G.two_internal_edges_of_missing_middle_fivePath
      hcritical heF hproper ha hb p hpLen hdk hdegree hthreshold
      (by simpa [hi] using hc)
  · exact G.two_internal_edges_of_missing_third_fivePath
      hcritical heF hproper ha hb p hpLen hdk hdegree hthreshold
      (by simpa [hi] using hc)
  · have hp4 : p.1.getVert 4 = G.snd e := by
      simpa [hpLen] using p.1.getVert_length
    have hvY : v = G.snd e := hi.symm.trans hp4
    exact G.two_internal_edges_of_missing_second_fivePath
      hcritical heF hproper ha hb p hpLen hdk hdegree hthreshold
      (by simpa [hvY] using hc)

end WeightedEdgeColoring.WeightedMultigraph
