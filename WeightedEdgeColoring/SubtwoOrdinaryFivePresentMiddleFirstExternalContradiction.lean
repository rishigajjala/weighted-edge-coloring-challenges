import WeightedEdgeColoring.SubtwoOrdinaryFivePresentMiddleFirstAllExternal

/-!
# One last-edge shift rules out the all-external middle-first case
-/

namespace WeightedEdgeColoring.WeightedMultigraph

universe u
variable (G : WeightedMultigraph.{u})

theorem FivePathState.false_of_middle_first_z2_external_z3
    {F : Finset G.E} {k D : ℕ} {a b c : Fin k}
    (s : G.FivePathState F k a b)
    (hcritical : G.IsColorCriticalOn F k)
    (hdk : D + 1 < k) (hdegree : ∀ z, G.degreeOn F z ≤ D)
    (hthreshold : 7 * D < 6 * k + 2)
    (hnot : FivePathState.NotTwoInternalColor G s c)
    (hleft : FivePathState.HasExternalColorAt G s c s.left)
    (hright : FivePathState.HasExternalColorAt G s c s.right)
    (hZ2 : FivePathState.HasExternalColorAt G s c
      (s.path.1.getVert 2))
    (hZ3 : FivePathState.HasExternalColorAt G s c
      (s.path.1.getVert 3))
    {z : G.V}
    (p : (G.twoColorGraph (F.erase s.omitted) s.paint b c).Path
      s.right z)
    {i : ℕ} (hi : 1 < i) (hiLe : i ≤ p.1.length)
    (hfirst : ∀ j, 0 < j → j < i →
      p.1.getVert j ∉ s.path.1.support.toFinset)
    (hiZ2 : p.1.getVert i = s.path.1.getVert 2) : False := by
  classical
  have hZ1 := FivePathState.external_at_z1_of_other_four_external
    G s hcritical hdk hdegree hthreshold hnot
      hleft hright hZ2 hZ3
  have hExtOld : ∀ v ∈ s.path.1.support.toFinset,
      FivePathState.HasExternalColorAt G s c v := by
    intro v hv
    have hS := FivePathState.support_eq_five_vertices G s
    rw [hS] at hv
    simp only [Finset.mem_insert, Finset.mem_singleton] at hv
    rcases hv with hX | h1 | h2 | h3 | hY
    · simpa [hX] using hleft
    · simpa [h1] using hZ1
    · simpa [h2] using hZ2
    · simpa [h3] using hZ3
    · simpa [hY] using hright
  obtain ⟨t, _, hinternal, hpaint, htL, htR, htS,
    ht1, ht2, ht3⟩ := FivePathState.exists_shiftLast G s hcritical
  have hcneA := (FivePathState.external_endpoint_color_ne_missing
    G s hleft hright).1
  have hnotT := FivePathState.not_two_internal_preserved_of_shiftLast
    G s t hcneA hpaint htS hnot
  have hExtT : ∀ v ∈ t.path.1.support.toFinset,
      FivePathState.HasExternalColorAt G t c v := by
    intro v hv
    exact FivePathState.external_preserved_of_shiftLast
      G s t hinternal hpaint htS
      (hExtOld v (by simpa [htS] using hv))
  have hExtL : FivePathState.HasExternalColorAt G t c t.left :=
    hExtT _ (by simpa only [List.mem_toFinset] using
      t.path.1.start_mem_support)
  have hExtR : FivePathState.HasExternalColorAt G t c t.right :=
    hExtT _ (by simpa only [List.mem_toFinset] using
      t.path.1.end_mem_support)
  have hExt1 : FivePathState.HasExternalColorAt G t c
      (t.path.1.getVert 1) :=
    hExtT _ (by simpa only [List.mem_toFinset] using
      t.path.1.getVert_mem_support 1)
  obtain ⟨q₀, hqLen, hqCap⟩ :=
    FivePathState.first_return_exterior_prefix G s p hiLe hfirst
      (hiZ2 ▸ by simpa only [List.mem_toFinset] using
        s.path.1.getVert_mem_support 2)
  have hZ3out : s.path.1.getVert 3 ∉ q₀.1.support := by
    intro hv
    have hS : s.path.1.getVert 3 ∈ s.path.1.support.toFinset := by
      simpa only [List.mem_toFinset] using
        s.path.1.getVert_mem_support 3
    rcases hqCap _ hv hS with hY | hZ2eq
    · exact (FivePathState.internal_vertex_ne_endpoints G s
        (by omega : 0 < 3) (by omega : 3 < 4)).2 hY
    · have hne := (s.path.1.adj_getVert_succ
        (i := 2) (by have := s.path_len; omega)).ne
      exact hne.symm (hZ2eq.trans hiZ2)
  have hInc : G.Inc (s.path.1.getVert 3) t.omitted :=
    htL.symm ▸ t.left_inc
  obtain ⟨qNew,hqSupport,_,_⟩ :=
    G.twoColorPath_after_shift_avoiding_removed_endpoint
      (a := a) hInc q₀ hZ3out
  have Hnew : G.twoColorGraph (F.erase t.omitted) t.paint b c =
      G.twoColorGraph (F.erase t.omitted)
        (G.assignEdgeColor s.paint s.omitted a) b c := by
    rw [hpaint]
  let qCast := G.pathCast Hnew qNew
  let pre0 := G.pathEndpointsCast rfl hiZ2.symm qCast
  let pre := G.pathEndpointsCast htR ht1 pre0
  have hpreCap : ∀ v ∈ pre.1.support,
      v ∈ t.path.1.support →
        v = t.right ∨ v = t.path.1.getVert 1 := by
    intro v hv hvT
    have hvOld : v ∈ q₀.1.support := by
      simpa [pre, pre0, qCast, G.pathEndpointsCast_support,
        G.pathCast_support, hqSupport] using hv
    have hvS : v ∈ s.path.1.support.toFinset := by
      rw [← htS]
      simpa only [List.mem_toFinset] using hvT
    rcases hqCap v hvOld hvS with hY | hZ2eq
    · exact Or.inl (hY.trans htR.symm)
    · exact Or.inr (hZ2eq.trans (hiZ2.trans ht1.symm))
  obtain ⟨p',i',hi',hiLe',hfirst',hi1'⟩ :=
    FivePathState.exists_first_return_at_one_of_exterior_prefix
      G t hcritical hdk hdegree hthreshold
      hExtL hExtR pre hpreCap
  have hnoMiddleT : ¬∃ g, g ∈ F.erase t.omitted ∧
      G.Inc (t.path.1.getVert 2) g ∧
      G.Inc (t.path.1.getVert 3) g ∧ t.paint g = c := by
    intro h
    obtain ⟨g,hgF,hg2,hg3,hgc⟩ := h
    have hne : t.path.1.getVert 2 ≠ t.path.1.getVert 3 :=
      (t.path.1.adj_getVert_succ
        (i := 2) (by have := t.path_len; omega)).ne
    have hEnds := G.endpoint_eq_or_endpoint_eq_swap_of_inc
      hne hg2 hg3
    have h2S : t.path.1.getVert 2 ∈
        t.path.1.support.toFinset := by
      simpa only [List.mem_toFinset] using
        t.path.1.getVert_mem_support 2
    have h3S : t.path.1.getVert 3 ∈
        t.path.1.support.toFinset := by
      simpa only [List.mem_toFinset] using
        t.path.1.getVert_mem_support 3
    have hgInt : g ∈ G.internalEdges (F.erase t.omitted)
        t.path.1.support.toFinset := by
      simp only [internalEdges, Finset.mem_filter]
      rcases hEnds with ⟨hf,hs⟩ | ⟨hf,hs⟩
      · exact ⟨hgF,hf.symm ▸ h2S,hs.symm ▸ h3S⟩
      · exact ⟨hgF,hf.symm ▸ h3S,hs.symm ▸ h2S⟩
    exact (FivePathState.no_internal_color_of_external_all
      G t hExtT g hgInt) hgc
  exact FivePathState.false_of_vz1_no_middle_c
    G t hcritical hdk hdegree hthreshold hnotT
      hExtL hExtR hExt1 hnoMiddleT p'
      hi' hiLe' hfirst' hi1'

end WeightedEdgeColoring.WeightedMultigraph
