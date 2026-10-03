import WeightedEdgeColoring.SubtwoOrdinaryFiveColors

/-!
# Colors missing at internal vertices of a critical five-chain
-/

namespace WeightedEdgeColoring.WeightedMultigraph

universe u
variable (G : WeightedMultigraph.{u})

/-- Orientation-independent two-edge saturation for a color missing at
the first vertex of an endpoint critical chain. -/
theorem two_internal_edges_of_missing_at_first_incident_endpoint
    {F : Finset G.E} {k d : ℕ} (hcritical : G.IsColorCriticalOn F k)
    {e : G.E} (heF : e ∈ F) {color : G.E → Fin k}
    (hproper : G.IsProperOn (F.erase e) color)
    {a b c : Fin k} {u v : G.V} (huv : u ≠ v)
    (heu : G.Inc u e) (hev : G.Inc v e)
    (ha : a ∈ G.missingColorsAt (F.erase e) color u)
    (hb : b ∈ G.missingColorsAt (F.erase e) color v)
    (hc : c ∈ G.missingColorsAt (F.erase e) color u)
    (q : (G.twoColorGraph (F.erase e) color a b).Path u v)
    (hqLen : q.1.length = 4)
    (hdk : d + 1 < k) (hdegree : ∀ z, G.degreeOn F z ≤ d)
    (hthreshold : 7 * d < 6 * k + 2) :
    ∃ g h, g ≠ h ∧
      g ∈ G.internalEdges (F.erase e) q.1.support.toFinset ∧
      h ∈ G.internalEdges (F.erase e) q.1.support.toFinset ∧
      color g = c ∧ color h = c := by
  have hends := G.endpoint_eq_or_endpoint_eq_swap_of_inc huv heu hev
  rcases hends with ⟨hfst, hsnd⟩ | ⟨hfst, hsnd⟩
  · let q' := G.pathEndpointsCast hfst hsnd q
    have hqLen' : q'.1.length = 4 := by
      rw [G.pathEndpointsCast_length]
      exact hqLen
    obtain ⟨g,h,hne,hg,hh,hgc,hhc⟩ :=
      G.two_internal_edges_of_missing_first_fivePath
        hcritical heF hproper (by simpa [hfst] using ha)
        (by simpa [hsnd] using hb) q' hqLen' hdk hdegree hthreshold
        (by simpa [hfst] using hc)
    have hsupport : q'.1.support.toFinset = q.1.support.toFinset := by
      rw [G.pathEndpointsCast_support]
    exact ⟨g,h,hne, by simpa [hsupport] using hg,
      by simpa [hsupport] using hh,hgc,hhc⟩
  · have hswap := G.twoColorGraph_swap color b a (F := F.erase e)
    let qr := G.pathCast hswap q.reverse
    let q' := G.pathEndpointsCast hfst hsnd qr
    have hqLen' : q'.1.length = 4 := by
      rw [G.pathEndpointsCast_length, G.pathCast_length]
      simpa using hqLen
    have hsupport : q'.1.support.toFinset = q.1.support.toFinset := by
      rw [G.pathEndpointsCast_support, G.pathCast_support]
      simp
    obtain ⟨g,h,hne,hg,hh,hgc,hhc⟩ :=
      G.two_internal_edges_of_missing_second_fivePath
        hcritical heF hproper (by simpa [hfst] using hb)
        (by simpa [hsnd] using ha) q' hqLen' hdk hdegree hthreshold
        (by simpa [hsnd] using hc)
    exact ⟨g,h,hne, by simpa [hsupport] using hg,
      by simpa [hsupport] using hh,hgc,hhc⟩

/-- A color missing at the third internal vertex occurs twice inside the
original five-chain. One omitted-edge shift makes that vertex an endpoint. -/
theorem two_internal_edges_of_missing_third_fivePath
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
    (hc : c ∈ G.missingColorsAt (F.erase e) color (p.1.getVert 3)) :
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
  have hca : c ≠ a := by
    intro h
    have hne := G.color_ne_of_mem_missingColorsAt
      (F.erase e) color (p.1.getVert 3) c hc hgF hgZ
    exact hne (hga.trans h.symm)
  have hcNew : c ∈ G.missingColorsAt (F.erase g)
      (G.assignEdgeColor color e a) (p.1.getVert 3) :=
    G.mem_missingColorsAt_shiftOmitted_of_ne hca hc
  have hZ3Y : p.1.getVert 3 ≠ G.snd e := by
    have h := G.criticalPath_last_internal p (by omega)
    simpa [hpLen] using h.2.2
  obtain ⟨r,s,hrs,hr,hs,hrc,hsc⟩ :=
    G.two_internal_edges_of_missing_at_first_incident_endpoint
      hcritical (Finset.mem_erase.mp hgF).2 hproperNew hZ3Y hgZ hgY
      haNew hbNew hcNew q hqLen hdk hdegree hthreshold
  have htransfer (t : G.E)
      (ht : t ∈ G.internalEdges (F.erase g) q.1.support.toFinset)
      (htc : G.assignEdgeColor color e a t = c) :
      t ∈ G.internalEdges (F.erase e) p.1.support.toFinset ∧
        color t = c := by
    have htData := Finset.mem_filter.mp ht
    have hte : t ≠ e := by
      intro heq
      have hac : a = c := by
        simpa [heq] using htc
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

/-- The corresponding two-edge conclusion for a color missing at the first
internal vertex follows by reversing stored edge orientations. -/
theorem two_internal_edges_of_missing_first_internal_fivePath
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
    (hc : c ∈ G.missingColorsAt (F.erase e) color (p.1.getVert 1)) :
    ∃ r s, r ≠ s ∧
      r ∈ G.internalEdges (F.erase e) p.1.support.toFinset ∧
      s ∈ G.internalEdges (F.erase e) p.1.support.toFinset ∧
      color r = c ∧ color s = c := by
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
  have hq3 : q.1.getVert 3 = p.1.getVert 1 := by
    rw [G.pathCast_getVert]
    change p.1.reverse.getVert 3 = p.1.getVert 1
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
  have hcR : c ∈ R.missingColorsAt (F.erase e) color (q.1.getVert 3) := by
    simpa [R, hq3] using hc
  obtain ⟨r,s,hrs,hr,hs,hrc,hsc⟩ :=
    R.two_internal_edges_of_missing_third_fivePath
      hcriticalR heF hproperR hbR haR q hqLen hdk hdegreeR
      hthreshold hcR
  exact ⟨r,s,hrs, by simpa [R, hqSupport] using hr,
    by simpa [R, hqSupport] using hs, hrc, hsc⟩

end WeightedEdgeColoring.WeightedMultigraph
