import WeightedEdgeColoring.SubtwoOrdinaryFivePresentDSharedEdge

/-!
# The second d edge in the original five-vertex support
-/

namespace WeightedEdgeColoring.WeightedMultigraph

universe u
variable (G : WeightedMultigraph.{u})

/-- Two disjoint edges of color `d` inside the old five-path, one of
which joins `Y` to `Z₁`, force the other to join `Z₂` to `Z₃`
when `d` is absent at `X`. -/
theorem second_internal_edge_joins_middle_vertices
    {F : Finset G.E} {k : ℕ} {paint : G.E → Fin k}
    (hproper : G.IsProperOn F paint)
    {S : Finset G.V} {x y z₁ z₂ z₃ : G.V}
    (hS : S = {x,z₁,z₂,z₃,y})
    {d : Fin k}
    (hdX : d ∈ G.missingColorsAt F paint x)
    {gY : G.E} (hgYF : gY ∈ F)
    (hgYY : G.Inc y gY) (hgYZ : G.Inc z₁ gY)
    (hgYD : paint gY = d)
    {r s : G.E} (hrs : r ≠ s)
    (hrI : r ∈ G.internalEdges F S)
    (hsI : s ∈ G.internalEdges F S)
    (hrD : paint r = d) (hsD : paint s = d) :
    ∃ g ∈ F, G.Inc z₂ g ∧ G.Inc z₃ g ∧ paint g = d := by
  have hchoose : ∃ g, g ∈ G.internalEdges F S ∧
      paint g = d ∧ g ≠ gY := by
    by_cases hrNe : r ≠ gY
    · exact ⟨r, hrI, hrD, hrNe⟩
    · have hrEq : r = gY := by simpa using hrNe
      exact ⟨s, hsI, hsD, by intro hsEq; exact hrs (hrEq.trans hsEq.symm)⟩
  obtain ⟨g, hgI, hgD, hgNeY⟩ := hchoose
  have hgData := Finset.mem_filter.mp hgI
  have hgF : g ∈ F := hgData.1
  have hgNotX : ¬G.Inc x g := by
    intro hgX
    exact (G.color_ne_of_mem_missingColorsAt F paint x d hdX hgF hgX) hgD
  have hgNotY : ¬G.Inc y g := by
    intro hgY
    have heq : g = gY := hproper y
      (Finset.mem_coe.mpr (Finset.mem_filter.mpr ⟨hgF, hgY⟩))
      (Finset.mem_coe.mpr (Finset.mem_filter.mpr ⟨hgYF, hgYY⟩))
      (hgD.trans hgYD.symm)
    exact hgNeY heq
  have hgNotZ₁ : ¬G.Inc z₁ g := by
    intro hgZ
    have heq : g = gY := hproper z₁
      (Finset.mem_coe.mpr (Finset.mem_filter.mpr ⟨hgF, hgZ⟩))
      (Finset.mem_coe.mpr (Finset.mem_filter.mpr ⟨hgYF, hgYZ⟩))
      (hgD.trans hgYD.symm)
    exact hgNeY heq
  have hfst : G.fst g = z₂ ∨ G.fst g = z₃ := by
    have h := hgData.2.1
    rw [hS] at h
    simp only [Finset.mem_insert, Finset.mem_singleton] at h
    rcases h with hx | hz₁ | hz₂ | hz₃ | hy
    · exact False.elim (hgNotX (Or.inl hx))
    · exact False.elim (hgNotZ₁ (Or.inl hz₁))
    · exact Or.inl hz₂
    · exact Or.inr hz₃
    · exact False.elim (hgNotY (Or.inl hy))
  have hsnd : G.snd g = z₂ ∨ G.snd g = z₃ := by
    have h := hgData.2.2
    rw [hS] at h
    simp only [Finset.mem_insert, Finset.mem_singleton] at h
    rcases h with hx | hz₁ | hz₂ | hz₃ | hy
    · exact False.elim (hgNotX (Or.inr hx))
    · exact False.elim (hgNotZ₁ (Or.inr hz₁))
    · exact Or.inl hz₂
    · exact Or.inr hz₃
    · exact False.elim (hgNotY (Or.inr hy))
  rcases hfst with hf₂ | hf₃
  · have hs₃ : G.snd g = z₃ := by
      rcases hsnd with hs₂ | hs₃
      · exact False.elim (G.noLoop g (hf₂.trans hs₂.symm))
      · exact hs₃
    exact ⟨g, hgF, Or.inl hf₂, Or.inr hs₃, hgD⟩
  · have hs₂ : G.snd g = z₂ := by
      rcases hsnd with hs₂ | hs₃
      · exact hs₂
      · exact False.elim (G.noLoop g (hf₃.trans hs₃.symm))
    exact ⟨g, hgF, Or.inr hs₂, Or.inl hf₃, hgD⟩

/-- Andersen's two-internal-edge lemma, packaged for either orientation
of a normalized five-path state. -/
theorem FivePathState.two_internal_edges_of_missing_left
    {F : Finset G.E} {k D : ℕ} {a b c : Fin k}
    (s : G.FivePathState F k a b)
    (hcritical : G.IsColorCriticalOn F k)
    (hdk : D + 1 < k) (hdegree : ∀ z, G.degreeOn F z ≤ D)
    (hthreshold : 7 * D < 6 * k + 2)
    (hcX : c ∈ G.missingColorsAt (F.erase s.omitted) s.paint s.left) :
    ∃ r t, r ≠ t ∧
      r ∈ G.internalEdges (F.erase s.omitted)
        s.path.1.support.toFinset ∧
      t ∈ G.internalEdges (F.erase s.omitted)
        s.path.1.support.toFinset ∧
      s.paint r = c ∧ s.paint t = c := by
  have hends := G.endpoint_eq_or_endpoint_eq_swap_of_inc
    s.left_ne_right s.left_inc s.right_inc
  rcases hends with ⟨hfst, hsnd⟩ | ⟨hfst, hsnd⟩
  · let p0 := G.pathEndpointsCast hfst hsnd s.path
    have hpLen : p0.1.length = 4 := by
      rw [G.pathEndpointsCast_length]
      exact s.path_len
    have hpSupport : p0.1.support = s.path.1.support :=
      G.pathEndpointsCast_support hfst hsnd s.path
    have ha0 : a ∈ G.missingColorsAt (F.erase s.omitted)
        s.paint (G.fst s.omitted) := by simpa [hfst] using s.left_missing
    have hb0 : b ∈ G.missingColorsAt (F.erase s.omitted)
        s.paint (G.snd s.omitted) := by simpa [hsnd] using s.right_missing
    have hc0 : c ∈ G.missingColorsAt (F.erase s.omitted)
        s.paint (G.fst s.omitted) := by simpa [hfst] using hcX
    have hv0 : G.fst s.omitted ∈ p0.1.support := by
      rw [hpSupport, hfst]
      exact s.path.1.start_mem_support
    obtain ⟨r,t,hrt,hrI,htI,hrc,htc⟩ :=
      G.two_internal_edges_of_missing_some_fivePath
        hcritical s.omitted_mem s.proper ha0 hb0 p0 hpLen
        hdk hdegree hthreshold hv0 hc0
    exact ⟨r,t,hrt,by simpa only [hpSupport] using hrI,
      by simpa only [hpSupport] using htI,hrc,htc⟩
  · let R := G.reverseEndpoints
    have hgraph : R.twoColorGraph (F.erase s.omitted) s.paint a b =
        G.twoColorGraph (F.erase s.omitted) s.paint a b := by
      exact (G.reverseEndpoints_twoColorGraph s.paint b a
        (F := F.erase s.omitted)).trans
        (G.twoColorGraph_swap s.paint b a (F := F.erase s.omitted))
    let p1 := G.pathCast hgraph s.path
    have hp1Len : p1.1.length = 4 := by
      rw [G.pathCast_length]
      exact s.path_len
    have hp1Support : p1.1.support = s.path.1.support :=
      G.pathCast_support hgraph s.path
    have hRf : R.fst s.omitted = s.left := by simpa [R] using hsnd
    have hRs : R.snd s.omitted = s.right := by simpa [R] using hfst
    let pR := G.pathEndpointsCast hRf hRs p1
    have hpRLen : pR.1.length = 4 := by
      rw [G.pathEndpointsCast_length]
      exact hp1Len
    have hpRSupport : pR.1.support = s.path.1.support := by
      rw [G.pathEndpointsCast_support, hp1Support]
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
    have hvR : R.fst s.omitted ∈ pR.1.support := by
      rw [hpRSupport, hRf]
      exact s.path.1.start_mem_support
    obtain ⟨r,t,hrt,hrI,htI,hrc,htc⟩ :=
      R.two_internal_edges_of_missing_some_fivePath
        hcriticalR s.omitted_mem hproperR haR hbR pR hpRLen
        hdk hdegreeR hthreshold hvR hcR
    exact ⟨r,t,hrt,by simpa [R, hpRSupport] using hrI,
      by simpa [R, hpRSupport] using htI,hrc,htc⟩

/-- Once `Y–Z₁` is a `d` edge, assertion (ii) pins the other
`d` edge of the old five-path at `Z₂–Z₃`. -/
theorem FivePathState.middle_d_edge_of_right_z1_edge
    {F : Finset G.E} {k D : ℕ} {a b d : Fin k}
    (s : G.FivePathState F k a b)
    (hcritical : G.IsColorCriticalOn F k)
    (hdk : D + 1 < k) (hdegree : ∀ z, G.degreeOn F z ≤ D)
    (hthreshold : 7 * D < 6 * k + 2)
    (hdX : d ∈ G.missingColorsAt (F.erase s.omitted) s.paint s.left)
    {gY : G.E} (hgYF : gY ∈ F.erase s.omitted)
    (hgYY : G.Inc s.right gY)
    (hgYZ : G.Inc (s.path.1.getVert 1) gY)
    (hgYD : s.paint gY = d) :
    ∃ g ∈ F.erase s.omitted,
      G.Inc (s.path.1.getVert 2) g ∧
      G.Inc (s.path.1.getVert 3) g ∧ s.paint g = d := by
  obtain ⟨r,t,hrt,hrI,htI,hrD,htD⟩ :=
    FivePathState.two_internal_edges_of_missing_left
      G s hcritical hdk hdegree hthreshold hdX
  exact G.second_internal_edge_joins_middle_vertices
    s.proper (FivePathState.support_eq_five_vertices G s)
    hdX hgYF hgYY hgYZ hgYD hrt hrI htI hrD htD

end WeightedEdgeColoring.WeightedMultigraph
