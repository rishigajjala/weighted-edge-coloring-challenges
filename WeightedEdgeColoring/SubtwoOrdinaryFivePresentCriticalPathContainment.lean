import WeightedEdgeColoring.SubtwoOrdinaryFivePresentBDCycle

/-!
# Critical path containment for an unoriented five-path state
-/

namespace WeightedEdgeColoring.WeightedMultigraph

universe u
variable (G : WeightedMultigraph.{u})

/-- Every critical endpoint path in the same coloring stays within a
five-vertex critical path, independent of the omitted edge's stored
orientation. -/
theorem FivePathState.other_critical_path_support_subset
    {F : Finset G.E} {k D : ℕ} {a b c f : Fin k}
    (s : G.FivePathState F k a b)
    (hcritical : G.IsColorCriticalOn F k)
    (hdk : D + 1 < k) (hdegree : ∀ z, G.degreeOn F z ≤ D)
    (hthreshold : 7 * D < 6 * k + 2)
    (hcX : c ∈ G.missingColorsAt (F.erase s.omitted) s.paint s.left)
    (hfY : f ∈ G.missingColorsAt (F.erase s.omitted) s.paint s.right)
    (q : (G.twoColorGraph (F.erase s.omitted) s.paint c f).Path
      s.left s.right) :
    q.1.support.toFinset ⊆ s.path.1.support.toFinset := by
  have hends := G.endpoint_eq_or_endpoint_eq_swap_of_inc
    s.left_ne_right s.left_inc s.right_inc
  rcases hends with ⟨hfst, hsnd⟩ | ⟨hfst, hsnd⟩
  · let p0 := G.pathEndpointsCast hfst hsnd s.path
    let q0 := G.pathEndpointsCast hfst hsnd q
    have hpLen : p0.1.length = 4 := by
      rw [G.pathEndpointsCast_length]
      exact s.path_len
    have hpSupport : p0.1.support = s.path.1.support :=
      G.pathEndpointsCast_support hfst hsnd s.path
    have hqSupport : q0.1.support = q.1.support :=
      G.pathEndpointsCast_support hfst hsnd q
    have ha0 : a ∈ G.missingColorsAt (F.erase s.omitted)
        s.paint (G.fst s.omitted) := by simpa [hfst] using s.left_missing
    have hb0 : b ∈ G.missingColorsAt (F.erase s.omitted)
        s.paint (G.snd s.omitted) := by simpa [hsnd] using s.right_missing
    have hc0 : c ∈ G.missingColorsAt (F.erase s.omitted)
        s.paint (G.fst s.omitted) := by simpa [hfst] using hcX
    have hf0 : f ∈ G.missingColorsAt (F.erase s.omitted)
        s.paint (G.snd s.omitted) := by simpa [hsnd] using hfY
    have hsub := G.criticalPath_support_subset_fivePath
      hcritical s.omitted_mem s.proper ha0 hb0 hc0 hf0
      p0 hpLen q0 hdk hdegree hthreshold
    simpa only [hpSupport, hqSupport] using hsub
  · let R := G.reverseEndpoints
    have hgraphP : R.twoColorGraph (F.erase s.omitted) s.paint a b =
        G.twoColorGraph (F.erase s.omitted) s.paint a b := by
      exact (G.reverseEndpoints_twoColorGraph s.paint b a
        (F := F.erase s.omitted)).trans
        (G.twoColorGraph_swap s.paint b a (F := F.erase s.omitted))
    have hgraphQ : R.twoColorGraph (F.erase s.omitted) s.paint c f =
        G.twoColorGraph (F.erase s.omitted) s.paint c f := by
      exact (G.reverseEndpoints_twoColorGraph s.paint f c
        (F := F.erase s.omitted)).trans
        (G.twoColorGraph_swap s.paint f c (F := F.erase s.omitted))
    let p1 := G.pathCast hgraphP s.path
    let q1 := G.pathCast hgraphQ q
    have hp1Len : p1.1.length = 4 := by
      rw [G.pathCast_length]
      exact s.path_len
    have hp1Support : p1.1.support = s.path.1.support :=
      G.pathCast_support hgraphP s.path
    have hq1Support : q1.1.support = q.1.support :=
      G.pathCast_support hgraphQ q
    have hRf : R.fst s.omitted = s.left := by simpa [R] using hsnd
    have hRs : R.snd s.omitted = s.right := by simpa [R] using hfst
    let pR := G.pathEndpointsCast hRf hRs p1
    let qR := G.pathEndpointsCast hRf hRs q1
    have hpRLen : pR.1.length = 4 := by
      rw [G.pathEndpointsCast_length]
      exact hp1Len
    have hpRSupport : pR.1.support = s.path.1.support := by
      rw [G.pathEndpointsCast_support, hp1Support]
    have hqRSupport : qR.1.support = q.1.support := by
      rw [G.pathEndpointsCast_support, hq1Support]
    have hproperR : R.IsProperOn (F.erase s.omitted) s.paint :=
      G.reverseEndpoints_proper_iff.mpr s.proper
    have hcriticalR : R.IsColorCriticalOn F k :=
      G.reverseEndpoints_critical_iff.mpr hcritical
    have hdegreeR : ∀ z, R.degreeOn F z ≤ D := by
      intro z
      simpa [R] using hdegree z
    have haR : a ∈ R.missingColorsAt (F.erase s.omitted)
        s.paint (R.fst s.omitted) := by simpa [R, hRf] using s.left_missing
    have hbR : b ∈ R.missingColorsAt (F.erase s.omitted)
        s.paint (R.snd s.omitted) := by simpa [R, hRs] using s.right_missing
    have hcR : c ∈ R.missingColorsAt (F.erase s.omitted)
        s.paint (R.fst s.omitted) := by simpa [R, hRf] using hcX
    have hfR : f ∈ R.missingColorsAt (F.erase s.omitted)
        s.paint (R.snd s.omitted) := by simpa [R, hRs] using hfY
    have hsub := R.criticalPath_support_subset_fivePath
      hcriticalR s.omitted_mem hproperR haR hbR hcR hfR
      pR hpRLen qR hdk hdegreeR hthreshold
    simpa only [hpRSupport, hqRSupport] using hsub

end WeightedEdgeColoring.WeightedMultigraph
