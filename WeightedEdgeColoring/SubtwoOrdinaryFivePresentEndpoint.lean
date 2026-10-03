import WeightedEdgeColoring.SubtwoOrdinaryFivePresentNormalize

/-!
# Endpoint normalization for an unsaturated present-everywhere color

This formalizes the symmetry reduction at the start of Andersen's
Theorem 5(iii): after shifting the omitted edge around the five-cycle,
the color under consideration leaves the chain at both endpoints.
-/

namespace WeightedEdgeColoring.WeightedMultigraph

universe u
variable (G : WeightedMultigraph.{u})

theorem unsaturated_color_has_recolored_external_endpoint_pair
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
    (hnot : ¬∃ r s, r ≠ s ∧
      r ∈ G.internalEdges (F.erase e) p.1.support.toFinset ∧
      s ∈ G.internalEdges (F.erase e) p.1.support.toFinset ∧
      color r = c ∧ color s = c) :
    ∃ a' b' : Fin k, ∃ t : G.FivePathState F k a' b',
      t.path.1.support.toFinset = p.1.support.toFinset ∧
      FivePathState.HasExternalColorAt G t c t.left ∧
      FivePathState.HasExternalColorAt G t c t.right ∧
      FivePathState.NotTwoInternalColor G t c := by
  let s : G.FivePathState F k a b := {
    omitted := e
    paint := color
    left := G.fst e
    right := G.snd e
    omitted_mem := heF
    left_ne_right := G.noLoop e
    left_inc := Or.inl rfl
    right_inc := Or.inr rfl
    proper := hproper
    left_missing := ha
    right_missing := hb
    path := p
    path_len := hpLen
  }
  have hpresent := G.present_at_every_fivePath_vertex_of_not_two_internal_edges
    hcritical heF hproper ha hb p hpLen hdk hdegree hthreshold hnot
  have hcneA : c ≠ a := by
    intro h
    exact hpresent _ p.1.start_mem_support (by simpa [h] using ha)
  have hcneB : c ≠ b := by
    intro h
    exact hpresent _ p.1.end_mem_support (by simpa [h] using hb)
  have hnotS : FivePathState.NotTwoInternalColor G s c := by
    simpa [FivePathState.NotTwoInternalColor, s] using hnot
  obtain ⟨i, hi, hinext⟩ :=
    G.unsaturated_color_has_adjacent_external_vertices
      hcritical heF hproper ha hb p hpLen hdk hdegree hthreshold hnot
  have hiExt : FivePathState.HasExternalColorAt G s c
      (p.1.getVert i.val) := by
    simpa [FivePathState.HasExternalColorAt, s] using hi
  have hnextExt : FivePathState.HasExternalColorAt G s c
      (p.1.getVert (i + 1).val) := by
    simpa [FivePathState.HasExternalColorAt, s] using hinext
  have hp4 : p.1.getVert 4 = G.snd e := by
    simpa [hpLen] using p.1.getVert_length
  have hpair :
      (FivePathState.HasExternalColorAt G s c s.left ∧
        FivePathState.HasExternalColorAt G s c s.right) ∨
      (FivePathState.HasExternalColorAt G s c s.left ∧
        FivePathState.HasExternalColorAt G s c (s.path.1.getVert 1)) ∨
      (FivePathState.HasExternalColorAt G s c (s.path.1.getVert 1) ∧
        FivePathState.HasExternalColorAt G s c (s.path.1.getVert 2)) ∨
      (FivePathState.HasExternalColorAt G s c (s.path.1.getVert 2) ∧
        FivePathState.HasExternalColorAt G s c (s.path.1.getVert 3)) ∨
      (FivePathState.HasExternalColorAt G s c (s.path.1.getVert 3) ∧
        FivePathState.HasExternalColorAt G s c s.right) := by
    fin_cases i
    · right; left
      exact ⟨by simpa [s] using hiExt, by simpa [s] using hnextExt⟩
    · right; right; left
      exact ⟨by simpa [s] using hiExt, by simpa [s] using hnextExt⟩
    · right; right; right; left
      exact ⟨by simpa [s] using hiExt, by simpa [s] using hnextExt⟩
    · right; right; right; right
      exact ⟨by simpa [s] using hiExt,
        by simpa [s, hp4] using hnextExt⟩
    · left
      exact ⟨by simpa [s] using hnextExt,
        by simpa [s, hp4] using hiExt⟩
  obtain ⟨a', b', t, hsupport, hleft, hright, hnotT⟩ :=
    FivePathState.exists_external_endpoint_state_of_cycle_pair
      G s hcritical hcneA hcneB hnotS hpair
  exact ⟨a', b', t, hsupport, hleft, hright, hnotT⟩

end WeightedEdgeColoring.WeightedMultigraph
