import WeightedEdgeColoring.SubtwoOrdinaryFivePresentRotate

/-!
# Repeated five-cycle shifts without relying on stored edge orientation

The omitted edge may be stored in either direction.  This theorem makes
the five-cycle shift invariant under that choice.
-/

namespace WeightedEdgeColoring.WeightedMultigraph

universe u
variable (G : WeightedMultigraph.{u})

theorem exists_last_shifted_fivePath_state_of_incident_endpoints
    {F : Finset G.E} {k : ℕ} (hcritical : G.IsColorCriticalOn F k)
    {e : G.E} (heF : e ∈ F) {color : G.E → Fin k}
    (hproper : G.IsProperOn (F.erase e) color)
    {a b : Fin k} {u v : G.V} (huv : u ≠ v)
    (heu : G.Inc u e) (hev : G.Inc v e)
    (ha : a ∈ G.missingColorsAt (F.erase e) color u)
    (hb : b ∈ G.missingColorsAt (F.erase e) color v)
    (p : (G.twoColorGraph (F.erase e) color a b).Path u v)
    (hpLen : p.1.length = 4) :
    ∃ g, g ∈ F.erase e ∧
      G.Inc (p.1.getVert 3) g ∧ G.Inc v g ∧ color g = a ∧
      G.IsProperOn (F.erase g) (G.assignEdgeColor color e a) ∧
      a ∈ G.missingColorsAt (F.erase g)
        (G.assignEdgeColor color e a) (p.1.getVert 3) ∧
      b ∈ G.missingColorsAt (F.erase g)
        (G.assignEdgeColor color e a) v ∧
      ∃ q : (G.twoColorGraph (F.erase g)
        (G.assignEdgeColor color e a) a b).Path (p.1.getVert 3) v,
        q.1.length = 4 ∧
        q.1.support.toFinset = p.1.support.toFinset ∧
        q.1.getVert 1 = p.1.getVert 2 ∧
        q.1.getVert 2 = p.1.getVert 1 ∧
        q.1.getVert 3 = u := by
  have hends := G.endpoint_eq_or_endpoint_eq_swap_of_inc huv heu hev
  rcases hends with ⟨hfst, hsnd⟩ | ⟨hfst, hsnd⟩
  · let p0 := G.pathEndpointsCast hfst hsnd p
    have hp0Len : p0.1.length = 4 := by
      rw [G.pathEndpointsCast_length]
      exact hpLen
    have hp0Vert (i : ℕ) : p0.1.getVert i = p.1.getVert i := by
      rw [G.pathEndpointsCast_getVert]
    have hp0Support : p0.1.support.toFinset = p.1.support.toFinset := by
      rw [G.pathEndpointsCast_support]
    have ha0 : a ∈ G.missingColorsAt (F.erase e) color (G.fst e) := by
      simpa [hfst] using ha
    have hb0 : b ∈ G.missingColorsAt (F.erase e) color (G.snd e) := by
      simpa [hsnd] using hb
    obtain ⟨g, hgF, hg3, hgv, hga, hproperNew, haNew,
        hbNew, q0, hq0Len, hq0Support, hq01, hq02, hq03⟩ :=
      G.exists_last_shifted_fivePath_state
        hcritical heF hproper ha0 hb0 p0 hp0Len
    let q := G.pathEndpointsCast (hp0Vert 3).symm hsnd.symm q0
    have hqVert (i : ℕ) : q.1.getVert i = q0.1.getVert i := by
      rw [G.pathEndpointsCast_getVert]
    have hqLen : q.1.length = 4 := by
      rw [G.pathEndpointsCast_length]
      exact hq0Len
    have hqSupport : q.1.support.toFinset = p.1.support.toFinset := by
      rw [G.pathEndpointsCast_support, hq0Support, hp0Support]
    refine ⟨g, hgF, ?_, ?_, hga, hproperNew, ?_, ?_,
      q, hqLen, hqSupport, ?_, ?_, ?_⟩
    · simpa [hp0Vert] using hg3
    · simpa [hsnd] using hgv
    · simpa [hp0Vert] using haNew
    · simpa [hsnd] using hbNew
    · exact (hqVert 1).trans (hq01.trans (hp0Vert 2))
    · exact (hqVert 2).trans (hq02.trans (hp0Vert 1))
    · exact (hqVert 3).trans (hq03.trans hfst)
  · let R := G.reverseEndpoints
    have hgraph : R.twoColorGraph (F.erase e) color a b =
        G.twoColorGraph (F.erase e) color a b := by
      exact (G.reverseEndpoints_twoColorGraph color b a).trans
        (G.twoColorGraph_swap color b a (F := F.erase e))
    let p1 := G.pathCast hgraph p
    have hp1Len : p1.1.length = 4 := by
      rw [G.pathCast_length]
      exact hpLen
    have hp1Vert (i : ℕ) : p1.1.getVert i = p.1.getVert i := by
      rw [G.pathCast_getVert]
    have hp1Support : p1.1.support.toFinset = p.1.support.toFinset := by
      rw [G.pathCast_support]
    have hRf : R.fst e = u := by simpa [R] using hsnd
    have hRs : R.snd e = v := by simpa [R] using hfst
    let pR := G.pathEndpointsCast hRf hRs p1
    have hpRLen : pR.1.length = 4 := by
      rw [G.pathEndpointsCast_length]
      exact hp1Len
    have hpRVert (i : ℕ) : pR.1.getVert i = p.1.getVert i := by
      rw [G.pathEndpointsCast_getVert, hp1Vert]
    have hpRSupport : pR.1.support.toFinset = p.1.support.toFinset := by
      rw [G.pathEndpointsCast_support, hp1Support]
    have hproperR : R.IsProperOn (F.erase e) color :=
      G.reverseEndpoints_proper_iff.mpr hproper
    have hcriticalR : R.IsColorCriticalOn F k :=
      G.reverseEndpoints_critical_iff.mpr hcritical
    have haR : a ∈ R.missingColorsAt (F.erase e) color (R.fst e) := by
      simpa [R, hRf] using ha
    have hbR : b ∈ R.missingColorsAt (F.erase e) color (R.snd e) := by
      simpa [R, hRs] using hb
    obtain ⟨g, hgF, hg3, hgv, hga, hproperNewR, haNewR,
        hbNewR, qR, hqRLen, hqRSupport, hqR1, hqR2, hqR3⟩ :=
      R.exists_last_shifted_fivePath_state
        hcriticalR heF hproperR haR hbR pR hpRLen
    have hgraphNew : R.twoColorGraph (F.erase g)
        (R.assignEdgeColor color e a) a b =
        G.twoColorGraph (F.erase g)
          (G.assignEdgeColor color e a) a b := by
      exact (G.reverseEndpoints_twoColorGraph
        (G.assignEdgeColor color e a) b a (F := F.erase g)).trans
        (G.twoColorGraph_swap
          (G.assignEdgeColor color e a) b a (F := F.erase g))
    let q1 := G.pathCast hgraphNew.symm qR
    let q := G.pathEndpointsCast (hpRVert 3).symm hRs.symm q1
    have hqVert (i : ℕ) : q.1.getVert i = qR.1.getVert i := by
      rw [G.pathEndpointsCast_getVert, G.pathCast_getVert]
    have hqLen : q.1.length = 4 := by
      rw [G.pathEndpointsCast_length, G.pathCast_length]
      exact hqRLen
    have hqSupport : q.1.support.toFinset = p.1.support.toFinset := by
      rw [G.pathEndpointsCast_support, G.pathCast_support,
        hqRSupport, hpRSupport]
    have hproperNew : G.IsProperOn (F.erase g)
        (G.assignEdgeColor color e a) := by
      exact G.reverseEndpoints_proper_iff.mp hproperNewR
    have hassign : R.assignEdgeColor color e a =
        G.assignEdgeColor color e a := rfl
    have haNew : a ∈ G.missingColorsAt (F.erase g)
        (G.assignEdgeColor color e a) (p.1.getVert 3) := by
      rw [hassign] at haNewR
      change a ∈ G.reverseEndpoints.missingColorsAt (F.erase g)
        (G.assignEdgeColor color e a) (pR.1.getVert 3) at haNewR
      rw [G.reverseEndpoints_missingColorsAt] at haNewR
      simpa [hpRVert] using haNewR
    have hbNew : b ∈ G.missingColorsAt (F.erase g)
        (G.assignEdgeColor color e a) v := by
      rw [hassign] at hbNewR
      change b ∈ G.reverseEndpoints.missingColorsAt (F.erase g)
        (G.assignEdgeColor color e a) (R.snd e) at hbNewR
      rw [G.reverseEndpoints_missingColorsAt] at hbNewR
      simpa [R, hRs] using hbNewR
    refine ⟨g, hgF, ?_, ?_, hga, hproperNew, haNew, hbNew,
      q, hqLen, hqSupport, ?_, ?_, ?_⟩
    · simpa [R, hpRVert] using hg3
    · simpa [R, hRs] using hgv
    · exact (hqVert 1).trans (hqR1.trans (hpRVert 2))
    · exact (hqVert 2).trans (hqR2.trans (hpRVert 1))
    · exact (hqVert 3).trans (hqR3.trans hRf)

end WeightedEdgeColoring.WeightedMultigraph
