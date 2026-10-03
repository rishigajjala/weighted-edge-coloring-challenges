import WeightedEdgeColoring.SubtwoOrdinaryFivePresentUnoriented

/-!
# An orientation-independent five-cycle recoloring state

This small structure packages the hypotheses that are preserved when the
omitted edge is shifted around a critical five-chain.
-/

namespace WeightedEdgeColoring.WeightedMultigraph

universe u

structure FivePathState (G : WeightedMultigraph.{u})
    (F : Finset G.E) (k : ℕ) (a b : Fin k) where
  omitted : G.E
  paint : G.E → Fin k
  left : G.V
  right : G.V
  omitted_mem : omitted ∈ F
  left_ne_right : left ≠ right
  left_inc : G.Inc left omitted
  right_inc : G.Inc right omitted
  proper : G.IsProperOn (F.erase omitted) paint
  left_missing : a ∈ G.missingColorsAt (F.erase omitted) paint left
  right_missing : b ∈ G.missingColorsAt (F.erase omitted) paint right
  path : (G.twoColorGraph (F.erase omitted) paint a b).Path left right
  path_len : path.1.length = 4

variable (G : WeightedMultigraph.{u})

noncomputable def FivePathState.reverse {F : Finset G.E} {k : ℕ} {a b : Fin k}
    (s : G.FivePathState F k a b) : G.FivePathState F k b a := by
  let hswap := G.twoColorGraph_swap s.paint b a (F := F.erase s.omitted)
  let p := G.pathCast hswap s.path.reverse
  have hpLen : p.1.length = 4 := by
    rw [G.pathCast_length]
    simpa using s.path_len
  exact {
    omitted := s.omitted
    paint := s.paint
    left := s.right
    right := s.left
    omitted_mem := s.omitted_mem
    left_ne_right := Ne.symm s.left_ne_right
    left_inc := s.right_inc
    right_inc := s.left_inc
    proper := s.proper
    left_missing := s.right_missing
    right_missing := s.left_missing
    path := p
    path_len := hpLen
  }

theorem FivePathState.reverse_support {F : Finset G.E} {k : ℕ}
    {a b : Fin k} (s : G.FivePathState F k a b) :
    (s.reverse.path.1.support.toFinset) = s.path.1.support.toFinset := by
  unfold FivePathState.reverse
  rw [G.pathCast_support]
  simp

theorem FivePathState.reverse_getVert {F : Finset G.E} {k : ℕ}
    {a b : Fin k} (s : G.FivePathState F k a b) (i : ℕ) :
    s.reverse.path.1.getVert i = s.path.1.getVert (4 - i) := by
  unfold FivePathState.reverse
  rw [G.pathCast_getVert]
  change s.path.1.reverse.getVert i = s.path.1.getVert (4 - i)
  rw [SimpleGraph.Walk.getVert_reverse, s.path_len]

/-- Shifting the omitted edge to the final colored edge of the path
produces another valid five-path state on the same vertex set. -/
theorem FivePathState.exists_shiftLast {F : Finset G.E} {k : ℕ}
    {a b : Fin k} (s : G.FivePathState F k a b)
    (hcritical : G.IsColorCriticalOn F k) :
    ∃ t : G.FivePathState F k a b,
      t.omitted ∈ F.erase s.omitted ∧
      t.omitted ∈ G.internalEdges (F.erase s.omitted)
        s.path.1.support.toFinset ∧
      t.paint = G.assignEdgeColor s.paint s.omitted a ∧
      t.left = s.path.1.getVert 3 ∧ t.right = s.right ∧
      t.path.1.support.toFinset = s.path.1.support.toFinset ∧
      t.path.1.getVert 1 = s.path.1.getVert 2 ∧
      t.path.1.getVert 2 = s.path.1.getVert 1 ∧
      t.path.1.getVert 3 = s.left := by
  obtain ⟨g, hgF, hg3, hgv, hga, hproperNew, haNew, hbNew,
      q, hqLen, hqSupport, hq1, hq2, hq3⟩ :=
    G.exists_last_shifted_fivePath_state_of_incident_endpoints
      hcritical s.omitted_mem s.proper s.left_ne_right
      s.left_inc s.right_inc s.left_missing s.right_missing
      s.path s.path_len
  have hp4 : s.path.1.getVert 4 = s.right := by
    simpa [s.path_len] using s.path.1.getVert_length
  have hne : s.path.1.getVert 3 ≠ s.right := by
    intro h
    have h34 : s.path.1.getVert 3 = s.path.1.getVert 4 := h.trans hp4.symm
    exact (by decide : (3 : ℕ) ≠ 4)
      (s.path.property.getVert_injOn
        (Set.mem_Iic.mpr (by have := s.path_len; omega))
        (Set.mem_Iic.mpr (by have := s.path_len; omega)) h34)
  have hgInternal : g ∈ G.internalEdges (F.erase s.omitted)
      s.path.1.support.toFinset := by
    have hends := G.endpoint_eq_or_endpoint_eq_swap_of_inc hne hg3 hgv
    have h3mem : s.path.1.getVert 3 ∈ s.path.1.support.toFinset := by
      simpa only [List.mem_toFinset] using s.path.1.getVert_mem_support 3
    have hrmem : s.right ∈ s.path.1.support.toFinset := by
      simpa only [List.mem_toFinset] using s.path.1.end_mem_support
    simp only [internalEdges, Finset.mem_filter]
    rcases hends with ⟨hfst, hsnd⟩ | ⟨hfst, hsnd⟩
    · exact ⟨hgF, hfst.symm ▸ h3mem, hsnd.symm ▸ hrmem⟩
    · exact ⟨hgF, hfst.symm ▸ hrmem, hsnd.symm ▸ h3mem⟩
  let t : G.FivePathState F k a b := {
    omitted := g
    paint := G.assignEdgeColor s.paint s.omitted a
    left := s.path.1.getVert 3
    right := s.right
    omitted_mem := (Finset.mem_erase.mp hgF).2
    left_ne_right := hne
    left_inc := hg3
    right_inc := hgv
    proper := hproperNew
    left_missing := haNew
    right_missing := hbNew
    path := q
    path_len := hqLen
  }
  exact ⟨t, hgF, hgInternal, rfl, rfl, rfl,
    hqSupport, hq1, hq2, hq3⟩

def FivePathState.HasExternalColorAt {F : Finset G.E} {k : ℕ}
    {a b : Fin k} (s : G.FivePathState F k a b)
    (c : Fin k) (v : G.V) : Prop :=
  ∃ g, g ∈ F.erase s.omitted ∧ G.Inc v g ∧ s.paint g = c ∧
    g ∉ G.internalEdges (F.erase s.omitted) s.path.1.support.toFinset

def FivePathState.NotTwoInternalColor {F : Finset G.E} {k : ℕ}
    {a b : Fin k} (s : G.FivePathState F k a b) (c : Fin k) : Prop :=
  ¬∃ r t, r ≠ t ∧
    r ∈ G.internalEdges (F.erase s.omitted) s.path.1.support.toFinset ∧
    t ∈ G.internalEdges (F.erase s.omitted) s.path.1.support.toFinset ∧
    s.paint r = c ∧ s.paint t = c

theorem FivePathState.reverse_not_two_internal
    {F : Finset G.E} {k : ℕ} {a b c : Fin k}
    (s : G.FivePathState F k a b)
    (h : FivePathState.NotTwoInternalColor G s c) :
    FivePathState.NotTwoInternalColor G s.reverse c := by
  intro htwo
  apply h
  obtain ⟨r, t, hne, hr, ht, hrc, htc⟩ := htwo
  exact ⟨r, t, hne,
    by simpa [s.reverse_support] using hr,
    by simpa [s.reverse_support] using ht,
    hrc, htc⟩

theorem FivePathState.not_two_internal_preserved_of_shiftLast
    {F : Finset G.E} {k : ℕ} {a b c : Fin k}
    (s t : G.FivePathState F k a b)
    (hcne : c ≠ a)
    (hpaint : t.paint = G.assignEdgeColor s.paint s.omitted a)
    (hsupport : t.path.1.support.toFinset =
      s.path.1.support.toFinset)
    (h : FivePathState.NotTwoInternalColor G s c) :
    FivePathState.NotTwoInternalColor G t c := by
  intro htwo
  obtain ⟨r, z, hrz, hr, hz, hrc, hzc⟩ := htwo
  have htransport {g : G.E}
      (hg : g ∈ G.internalEdges (F.erase t.omitted)
        t.path.1.support.toFinset)
      (hgc : t.paint g = c) :
      g ∈ G.internalEdges (F.erase s.omitted)
        s.path.1.support.toFinset ∧ s.paint g = c := by
    have hgne : g ≠ s.omitted := by
      intro heq
      have hnew : t.paint g = a := by
        rw [hpaint, heq]
        simp [assignEdgeColor]
      exact hcne (hgc.symm.trans hnew)
    have hgF : g ∈ F := (Finset.mem_erase.mp
      (Finset.mem_filter.mp hg).1).2
    have hgOld : g ∈ G.internalEdges (F.erase s.omitted)
        s.path.1.support.toFinset := by
      simp only [internalEdges, Finset.mem_filter] at hg ⊢
      exact ⟨Finset.mem_erase.mpr ⟨hgne, hgF⟩,
        by simpa [hsupport] using hg.2⟩
    have hgcOld : s.paint g = c := by
      rw [hpaint, G.assignEdgeColor_of_ne s.paint hgne a] at hgc
      exact hgc
    exact ⟨hgOld, hgcOld⟩
  obtain ⟨hrOld, hrcOld⟩ := htransport hr hrc
  obtain ⟨hzOld, hzcOld⟩ := htransport hz hzc
  exact h ⟨r, z, hrz, hrOld, hzOld, hrcOld, hzcOld⟩

theorem FivePathState.reverse_external {F : Finset G.E} {k : ℕ}
    {a b c : Fin k} (s : G.FivePathState F k a b) {v : G.V}
    (h : FivePathState.HasExternalColorAt G s c v) :
    FivePathState.HasExternalColorAt G s.reverse c v := by
  obtain ⟨g, hgF, hgv, hgc, hgExt⟩ := h
  refine ⟨g, hgF, hgv, hgc, ?_⟩
  simpa [s.reverse_support] using hgExt

theorem FivePathState.external_preserved_of_shiftLast
    {F : Finset G.E} {k : ℕ} {a b c : Fin k}
    (s t : G.FivePathState F k a b) {v : G.V}
    (hinternal : t.omitted ∈ G.internalEdges (F.erase s.omitted)
      s.path.1.support.toFinset)
    (hpaint : t.paint = G.assignEdgeColor s.paint s.omitted a)
    (hsupport : t.path.1.support.toFinset =
      s.path.1.support.toFinset)
    (h : FivePathState.HasExternalColorAt G s c v) :
    FivePathState.HasExternalColorAt G t c v := by
  obtain ⟨g, hgF, hgv, hgc, hgExt⟩ := h
  obtain ⟨hgNew, hgcNew, hgExtNew⟩ :=
    G.external_colored_edge_transport_erase_swap
      hgF hgExt hgc hinternal
  refine ⟨g, hgNew, hgv, ?_, ?_⟩
  · simpa [hpaint] using hgcNew
  · simpa [hsupport] using hgExtNew

theorem FivePathState.exists_shiftLast_preserving_external
    {F : Finset G.E} {k : ℕ} {a b c : Fin k}
    (s : G.FivePathState F k a b)
    (hcritical : G.IsColorCriticalOn F k)
    {u v : G.V}
    (hu : FivePathState.HasExternalColorAt G s c u)
    (hv : FivePathState.HasExternalColorAt G s c v) :
    ∃ t : G.FivePathState F k a b,
      t.paint = G.assignEdgeColor s.paint s.omitted a ∧
      t.left = s.path.1.getVert 3 ∧ t.right = s.right ∧
      t.path.1.support.toFinset = s.path.1.support.toFinset ∧
      t.path.1.getVert 1 = s.path.1.getVert 2 ∧
      t.path.1.getVert 2 = s.path.1.getVert 1 ∧
      t.path.1.getVert 3 = s.left ∧
      FivePathState.HasExternalColorAt G t c u ∧
      FivePathState.HasExternalColorAt G t c v := by
  obtain ⟨t, _, hinternal, hpaint, hleft, hright,
      hsupport, hq1, hq2, hq3⟩ :=
    FivePathState.exists_shiftLast G s hcritical
  have huT := FivePathState.external_preserved_of_shiftLast
    G s t hinternal hpaint hsupport hu
  have hvT := FivePathState.external_preserved_of_shiftLast
    G s t hinternal hpaint hsupport hv
  exact ⟨t, hpaint, hleft, hright, hsupport,
    hq1, hq2, hq3, huT, hvT⟩

/-- The last-edge shift also preserves a shortage of internal edges in
any color other than the color assigned to the formerly omitted edge. -/
theorem FivePathState.exists_shiftLast_preserving_external_not_two
    {F : Finset G.E} {k : ℕ} {a b c : Fin k}
    (s : G.FivePathState F k a b)
    (hcritical : G.IsColorCriticalOn F k)
    (hcne : c ≠ a)
    {u v : G.V}
    (hu : FivePathState.HasExternalColorAt G s c u)
    (hv : FivePathState.HasExternalColorAt G s c v)
    (hnot : FivePathState.NotTwoInternalColor G s c) :
    ∃ t : G.FivePathState F k a b,
      t.paint = G.assignEdgeColor s.paint s.omitted a ∧
      t.left = s.path.1.getVert 3 ∧ t.right = s.right ∧
      t.path.1.support.toFinset = s.path.1.support.toFinset ∧
      t.path.1.getVert 1 = s.path.1.getVert 2 ∧
      t.path.1.getVert 2 = s.path.1.getVert 1 ∧
      t.path.1.getVert 3 = s.left ∧
      FivePathState.HasExternalColorAt G t c u ∧
      FivePathState.HasExternalColorAt G t c v ∧
      FivePathState.NotTwoInternalColor G t c := by
  obtain ⟨t, _, hinternal, hpaint, hleft, hright,
      hsupport, hq1, hq2, hq3⟩ :=
    FivePathState.exists_shiftLast G s hcritical
  have huT := FivePathState.external_preserved_of_shiftLast
    G s t hinternal hpaint hsupport hu
  have hvT := FivePathState.external_preserved_of_shiftLast
    G s t hinternal hpaint hsupport hv
  have hnotT := FivePathState.not_two_internal_preserved_of_shiftLast
    G s t hcne hpaint hsupport hnot
  exact ⟨t, hpaint, hleft, hright, hsupport,
    hq1, hq2, hq3, huT, hvT, hnotT⟩

end WeightedEdgeColoring.WeightedMultigraph
