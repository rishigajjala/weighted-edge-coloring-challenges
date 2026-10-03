import WeightedEdgeColoring.SubtwoOrdinaryFivePresentDIntersection

/-!
# The d edge shared by the old and switched critical paths
-/

namespace WeightedEdgeColoring.WeightedMultigraph

universe u
variable (G : WeightedMultigraph.{u})

/-- When the `d` edge at `Y` survives recoloring, the two critical
five-path supports force that edge to join `Y` to `Z₁`. -/
theorem FivePathState.right_d_edge_to_common_z1
    {F : Finset G.E} {k D : ℕ} {a b c d : Fin k}
    (s : G.FivePathState F k a b)
    (hcritical : G.IsColorCriticalOn F k)
    (hdk : D + 1 < k) (hdegree : ∀ z, G.degreeOn F z ≤ D)
    (hthreshold : 7 * D < 6 * k + 2)
    (hdX : d ∈ G.missingColorsAt (F.erase s.omitted) s.paint s.left)
    (hdY : d ∉ G.missingColorsAt (F.erase s.omitted) s.paint s.right)
    {paint₂ : G.E → Fin k}
    (hproper₂ : G.IsProperOn (F.erase s.omitted) paint₂)
    (hcX₂ : c ∈ G.missingColorsAt (F.erase s.omitted) paint₂ s.left)
    (haY₂ : a ∈ G.missingColorsAt (F.erase s.omitted) paint₂ s.right)
    (hdX₂ : d ∈ G.missingColorsAt (F.erase s.omitted) paint₂ s.left)
    (hkeep : ∀ g ∈ F.erase s.omitted,
      s.paint g = d → paint₂ g = d)
    (q : (G.twoColorGraph (F.erase s.omitted) paint₂ c a).Path
      s.left s.right)
    (hqLen : q.1.length = 4)
    {z w u : G.V}
    (hqSupport : q.1.support.toFinset = {s.left,z,w,u,s.right})
    (hwOut : w ∉ s.path.1.support.toFinset)
    (huOut : u ∉ s.path.1.support.toFinset) :
    ∃ g ∈ F.erase s.omitted,
      G.Inc s.right g ∧ G.Inc z g ∧ s.paint g = d := by
  let s₂ : G.FivePathState F k c a := {
    omitted := s.omitted
    paint := paint₂
    left := s.left
    right := s.right
    omitted_mem := s.omitted_mem
    left_ne_right := s.left_ne_right
    left_inc := s.left_inc
    right_inc := s.right_inc
    proper := hproper₂
    left_missing := hcX₂
    right_missing := haY₂
    path := q
    path_len := hqLen
  }
  obtain ⟨g, hgF, hgY, hgD⟩ :=
    G.exists_edge_of_not_missingColor hdY
  have hgS : g ∈ G.internalEdges (F.erase s.omitted)
      s.path.1.support.toFinset :=
    FivePathState.right_color_edge_internal_of_missing_left
      G s hcritical hdk hdegree hthreshold hdX hgF hgY hgD
  have hg₂D : paint₂ g = d := hkeep g hgF hgD
  have hgT : g ∈ G.internalEdges (F.erase s.omitted)
      q.1.support.toFinset := by
    have h := FivePathState.right_color_edge_internal_of_missing_left
      G s₂ hcritical hdk hdegree hthreshold hdX₂ hgF hgY hg₂D
    simpa [s₂] using h
  have hgNotX : ¬G.Inc s.left g := by
    intro hgX
    exact (G.color_ne_of_mem_missingColorsAt
      (F.erase s.omitted) s.paint s.left d hdX hgF hgX) hgD
  have hinter := G.old_new_five_support_intersection
    hwOut huOut q hqSupport
  have hgZ : G.Inc z g :=
    G.internal_edge_in_two_supports_at_right
      hinter hgS hgT hgY hgNotX
  exact ⟨g, hgF, hgY, hgZ, hgD⟩

/-- The degree gap gives a second missing color at the left endpoint. -/
theorem FivePathState.exists_second_missing_left_color
    {F : Finset G.E} {k D : ℕ} {a b c : Fin k}
    (s : G.FivePathState F k a b)
    (hdk : D + 1 < k) (hdegree : ∀ z, G.degreeOn F z ≤ D) :
    ∃ d ∈ G.missingColorsAt (F.erase s.omitted) s.paint s.left,
      d ≠ c := by
  classical
  let M := G.missingColorsAt (F.erase s.omitted) s.paint s.left
  have hcard : 1 < M.card := by
    dsimp [M]
    rw [G.card_missingColorsAt (F.erase s.omitted) s.paint s.proper]
    have hdeg := hdegree s.left
    have hdegErase := G.degreeOn_mono_critical
      (Finset.erase_subset s.omitted F) s.left
    omega
  by_contra hnone
  have hsub : M ⊆ {c} := by
    intro d hd
    by_contra hne
    exact hnone ⟨d, hd, by simpa using hne⟩
  have hle : M.card ≤ 1 := by
    have h := Finset.card_le_card hsub
    simpa using h
  omega

/-- Any color missing at one endpoint of a critical omitted edge is
present at the other endpoint, independently of its stored orientation. -/
theorem FivePathState.missing_left_color_present_right
    {F : Finset G.E} {k : ℕ} {a b d : Fin k}
    (s : G.FivePathState F k a b)
    (hcritical : G.IsColorCriticalOn F k)
    (hdX : d ∈ G.missingColorsAt (F.erase s.omitted) s.paint s.left) :
    d ∉ G.missingColorsAt (F.erase s.omitted) s.paint s.right := by
  intro hdY
  have hends := G.endpoint_eq_or_endpoint_eq_swap_of_inc
    s.left_ne_right s.left_inc s.right_inc
  rcases hends with ⟨hfst, hsnd⟩ | ⟨hfst, hsnd⟩
  · have hx : d ∈ G.missingColorsAt (F.erase s.omitted) s.paint
        (G.fst s.omitted) := by simpa [hfst] using hdX
    have hy : d ∈ G.missingColorsAt (F.erase s.omitted) s.paint
        (G.snd s.omitted) := by simpa [hsnd] using hdY
    exact (G.critical_endpoint_missingColors_ne
      hcritical s.omitted_mem s.proper hx hy) rfl
  · let R := G.reverseEndpoints
    have hcriticalR : R.IsColorCriticalOn F k :=
      G.reverseEndpoints_critical_iff.mpr hcritical
    have hproperR : R.IsProperOn (F.erase s.omitted) s.paint :=
      G.reverseEndpoints_proper_iff.mpr s.proper
    have hRf : R.fst s.omitted = s.left := by simpa [R] using hsnd
    have hRs : R.snd s.omitted = s.right := by simpa [R] using hfst
    have hx : d ∈ R.missingColorsAt (F.erase s.omitted) s.paint
        (R.fst s.omitted) := by simpa [R, hRf] using hdX
    have hy : d ∈ R.missingColorsAt (F.erase s.omitted) s.paint
        (R.snd s.omitted) := by simpa [R, hRs] using hdY
    exact (R.critical_endpoint_missingColors_ne
      hcriticalR s.omitted_mem hproperR hx hy) rfl

end WeightedEdgeColoring.WeightedMultigraph
