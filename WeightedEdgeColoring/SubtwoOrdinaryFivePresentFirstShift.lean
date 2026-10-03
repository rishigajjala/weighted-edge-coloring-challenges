import WeightedEdgeColoring.SubtwoOrdinaryFivePresentShift

/-! The mirror of boundary-edge transport through the last omitted-edge shift. -/

namespace WeightedEdgeColoring.WeightedMultigraph

universe u
variable (G : WeightedMultigraph.{u})

/-- A boundary-color pair at `Z₁,X` becomes an endpoint pair after
shifting the omitted edge from `X,Y` to the first path edge. -/
theorem external_endpoint_pair_of_shifted_first_edge_fivePath
    {F : Finset G.E} {k : ℕ} (hcritical : G.IsColorCriticalOn F k)
    {e : G.E} (heF : e ∈ F) {color : G.E → Fin k}
    (hproper : G.IsProperOn (F.erase e) color)
    {a b c : Fin k}
    (ha : a ∈ G.missingColorsAt (F.erase e) color (G.fst e))
    (hb : b ∈ G.missingColorsAt (F.erase e) color (G.snd e))
    (p : (G.twoColorGraph (F.erase e) color a b).Path
      (G.fst e) (G.snd e)) (hpLen : p.1.length = 4)
    {g r s : G.E} (hgF : g ∈ F.erase e)
    (hgZ : G.Inc (p.1.getVert 1) g)
    (hgX : G.Inc (G.fst e) g) (hgb : color g = b)
    (hrF : r ∈ F.erase e) (hrZ : G.Inc (p.1.getVert 1) r)
    (hrColor : color r = c)
    (hrExternal : r ∉ G.internalEdges (F.erase e) p.1.support.toFinset)
    (hsF : s ∈ F.erase e) (hsX : G.Inc (G.fst e) s)
    (hsColor : color s = c)
    (hsExternal : s ∉ G.internalEdges (F.erase e) p.1.support.toFinset) :
    ∃ q : (G.twoColorGraph (F.erase g)
      (G.assignEdgeColor color e b) a b).Path
        (p.1.getVert 1) (G.fst e),
      q.1.length = 4 ∧
      q.1.support.toFinset = p.1.support.toFinset ∧
      r ∈ F.erase g ∧ G.Inc (q.1.getVert 0) r ∧
      G.assignEdgeColor color e b r = c ∧
      r ∉ G.internalEdges (F.erase g) q.1.support.toFinset ∧
      s ∈ F.erase g ∧ G.Inc (q.1.getVert 4) s ∧
      G.assignEdgeColor color e b s = c ∧
      s ∉ G.internalEdges (F.erase g) q.1.support.toFinset := by
  let R := G.reverseEndpoints
  have hgraph : R.twoColorGraph (F.erase e) color b a =
      G.twoColorGraph (F.erase e) color a b :=
    G.reverseEndpoints_twoColorGraph color a b
  let pR : (R.twoColorGraph (F.erase e) color b a).Path
      (R.fst e) (R.snd e) := G.pathCast hgraph p.reverse
  have hpRLen : pR.1.length = 4 := by
    rw [G.pathCast_length]
    simpa using hpLen
  have hpRSupport : pR.1.support.toFinset = p.1.support.toFinset := by
    rw [G.pathCast_support]
    simp
  have hpR3 : pR.1.getVert 3 = p.1.getVert 1 := by
    rw [G.pathCast_getVert]
    change p.1.reverse.getVert 3 = p.1.getVert 1
    rw [SimpleGraph.Walk.getVert_reverse, hpLen]
  have hproperR : R.IsProperOn (F.erase e) color :=
    G.reverseEndpoints_proper_iff.mpr hproper
  have hcriticalR : R.IsColorCriticalOn F k :=
    G.reverseEndpoints_critical_iff.mpr hcritical
  have hbR : b ∈ R.missingColorsAt (F.erase e) color (R.fst e) := by
    simpa [R] using hb
  have haR : a ∈ R.missingColorsAt (F.erase e) color (R.snd e) := by
    simpa [R] using ha
  have hgZR : R.Inc (pR.1.getVert 3) g := by
    simpa [R, hpR3] using hgZ
  have hgXR : R.Inc (R.snd e) g := by
    simpa [R] using hgX
  have hrZR : R.Inc (pR.1.getVert 3) r := by
    simpa [R, hpR3] using hrZ
  have hsXR : R.Inc (R.snd e) s := by
    simpa [R] using hsX
  have hrExtR : r ∉ R.internalEdges (F.erase e) pR.1.support.toFinset := by
    simpa [R, hpRSupport] using hrExternal
  have hsExtR : s ∉ R.internalEdges (F.erase e) pR.1.support.toFinset := by
    simpa [R, hpRSupport] using hsExternal
  obtain ⟨qR, hqRLen, hqRSupport, hrNew, hrInc, hrNewColor,
      hrNewExt, hsNew, hsInc, hsNewColor, hsNewExt⟩ :=
    R.external_endpoint_pair_of_shifted_last_edge_fivePath
      hcriticalR heF hproperR hbR haR pR hpRLen
      hgF hgZR hgXR hgb hrF hrZR hrColor hrExtR
      hsF hsXR hsColor hsExtR
  have hgraphNew : R.twoColorGraph (F.erase g)
      (R.assignEdgeColor color e b) b a =
      G.twoColorGraph (F.erase g)
        (G.assignEdgeColor color e b) a b := by
    simpa [R] using
      (G.reverseEndpoints_twoColorGraph
        (G.assignEdgeColor color e b) a b (F := F.erase g))
  let q0 := G.pathCast hgraphNew.symm qR
  let q : (G.twoColorGraph (F.erase g)
      (G.assignEdgeColor color e b) a b).Path
        (p.1.getVert 1) (G.fst e) :=
    G.pathEndpointsCast hpR3.symm (by rfl) q0
  have hqVert (i : ℕ) : q.1.getVert i = qR.1.getVert i := by
    rw [G.pathEndpointsCast_getVert, G.pathCast_getVert]
  have hqLen : q.1.length = 4 := by
    rw [G.pathEndpointsCast_length, G.pathCast_length]
    exact hqRLen
  have hqSupport : q.1.support.toFinset = p.1.support.toFinset := by
    rw [G.pathEndpointsCast_support, G.pathCast_support,
      hqRSupport, hpRSupport]
  refine ⟨q, hqLen, hqSupport, hrNew, ?_, ?_, ?_,
    hsNew, ?_, ?_, ?_⟩
  · simpa [R, hqVert] using hrInc
  · simpa [R] using hrNewColor
  · simpa [R, hqSupport, hqRSupport, hpRSupport] using hrNewExt
  · simpa [R, hqVert] using hsInc
  · simpa [R] using hsNewColor
  · simpa [R, hqSupport, hqRSupport, hpRSupport] using hsNewExt

end WeightedEdgeColoring.WeightedMultigraph
