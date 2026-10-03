import WeightedEdgeColoring.SubtwoOrdinaryFivePresentEndpoint

/-!
# Present colors remain present after five-cycle normalization
-/

namespace WeightedEdgeColoring.WeightedMultigraph

universe u
variable (G : WeightedMultigraph.{u})

/-- The missing-color saturation theorem applies to a five-path state even
when its omitted edge is stored with the opposite endpoint orientation. -/
theorem FivePathState.present_at_every_vertex_of_not_two_internal
    {F : Finset G.E} {k d : ℕ} {a b c : Fin k}
    (s : G.FivePathState F k a b)
    (hcritical : G.IsColorCriticalOn F k)
    (hdk : d + 1 < k) (hdegree : ∀ z, G.degreeOn F z ≤ d)
    (hthreshold : 7 * d < 6 * k + 2)
    (hnot : FivePathState.NotTwoInternalColor G s c) :
    ∀ v ∈ s.path.1.support,
      c ∉ G.missingColorsAt (F.erase s.omitted) s.paint v := by
  have hends := G.endpoint_eq_or_endpoint_eq_swap_of_inc
    s.left_ne_right s.left_inc s.right_inc
  rcases hends with ⟨hfst, hsnd⟩ | ⟨hfst, hsnd⟩
  · let p0 := G.pathEndpointsCast hfst hsnd s.path
    have hp0Len : p0.1.length = 4 := by
      rw [G.pathEndpointsCast_length]
      exact s.path_len
    have hp0Support : p0.1.support = s.path.1.support := by
      exact G.pathEndpointsCast_support hfst hsnd s.path
    have ha0 : a ∈ G.missingColorsAt (F.erase s.omitted)
        s.paint (G.fst s.omitted) := by simpa [hfst] using s.left_missing
    have hb0 : b ∈ G.missingColorsAt (F.erase s.omitted)
        s.paint (G.snd s.omitted) := by simpa [hsnd] using s.right_missing
    have hnot0 : ¬∃ r t, r ≠ t ∧
        r ∈ G.internalEdges (F.erase s.omitted) p0.1.support.toFinset ∧
        t ∈ G.internalEdges (F.erase s.omitted) p0.1.support.toFinset ∧
        s.paint r = c ∧ s.paint t = c := by
      simpa only [hp0Support, FivePathState.NotTwoInternalColor] using hnot
    intro v hv
    exact G.present_at_every_fivePath_vertex_of_not_two_internal_edges
      hcritical s.omitted_mem s.proper ha0 hb0 p0 hp0Len
      hdk hdegree hthreshold hnot0 v (by simpa [hp0Support] using hv)
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
    have hp1Support : p1.1.support = s.path.1.support := by
      exact G.pathCast_support hgraph s.path
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
    have hdegreeR : ∀ z, R.degreeOn F z ≤ d := by
      intro z
      simpa [R] using hdegree z
    have haR : a ∈ R.missingColorsAt (F.erase s.omitted)
        s.paint (R.fst s.omitted) := by simpa [R, hRf] using s.left_missing
    have hbR : b ∈ R.missingColorsAt (F.erase s.omitted)
        s.paint (R.snd s.omitted) := by simpa [R, hRs] using s.right_missing
    have hnotR : ¬∃ r t, r ≠ t ∧
        r ∈ R.internalEdges (F.erase s.omitted) pR.1.support.toFinset ∧
        t ∈ R.internalEdges (F.erase s.omitted) pR.1.support.toFinset ∧
        s.paint r = c ∧ s.paint t = c := by
      simpa [R, hpRSupport, FivePathState.NotTwoInternalColor] using hnot
    intro v hv
    have hcR := R.present_at_every_fivePath_vertex_of_not_two_internal_edges
      hcriticalR s.omitted_mem hproperR haR hbR pR hpRLen
      hdk hdegreeR hthreshold hnotR v (by simpa [hpRSupport] using hv)
    change c ∉ G.reverseEndpoints.missingColorsAt
      (F.erase s.omitted) s.paint v at hcR
    rw [G.reverseEndpoints_missingColorsAt] at hcR
    exact hcR

/-- An unsaturated color can be normalized to both omitted-edge endpoints
without losing either its internal-edge shortage or presence on the chain. -/
theorem unsaturated_color_has_present_external_endpoint_state
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
      FivePathState.NotTwoInternalColor G t c ∧
      ∀ v ∈ t.path.1.support,
        c ∉ G.missingColorsAt (F.erase t.omitted) t.paint v := by
  obtain ⟨a', b', t, hsupport, hleft, hright, hnotT⟩ :=
    G.unsaturated_color_has_recolored_external_endpoint_pair
      hcritical heF hproper ha hb p hpLen hdk hdegree hthreshold hnot
  exact ⟨a', b', t, hsupport, hleft, hright, hnotT,
    FivePathState.present_at_every_vertex_of_not_two_internal G t
      hcritical hdk hdegree hthreshold hnotT⟩

/-- The cycle-neighbor pigeonhole step only uses that the path is simple
and has five vertices. -/
theorem fivePath_three_vertices_have_cycle_neighbor_pair_unoriented
    {H : SimpleGraph G.V} {x y : G.V}
    (p : H.Path x y) (hpLen : p.1.length = 4)
    (T : Finset G.V) (hTsub : T ⊆ p.1.support.toFinset)
    (hTcard : 3 ≤ T.card) :
    ∃ i : Fin 5,
      p.1.getVert i.val ∈ T ∧ p.1.getVert (i + 1).val ∈ T := by
  classical
  let f : Fin 5 → G.V := fun i ↦ p.1.getVert i.val
  have hf : Function.Injective f := by
    intro i j hij
    apply Fin.ext
    exact p.property.getVert_injOn
      (Set.mem_Iic.mpr (by have := i.isLt; omega))
      (Set.mem_Iic.mpr (by have := j.isLt; omega)) hij
  have hsubImage : (Finset.univ.image f) ⊆ p.1.support.toFinset := by
    intro v hv
    obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hv
    change p.1.getVert i.val ∈ p.1.support.toFinset
    simpa only [List.mem_toFinset] using p.1.getVert_mem_support i.val
  have himageCard : (Finset.univ.image f).card = 5 := by
    rw [Finset.card_image_of_injective _ hf]
    simp
  have hpCard : p.1.support.toFinset.card = 5 := by
    rw [List.toFinset_card_of_nodup p.property.support_nodup,
      p.1.length_support, hpLen]
  have himage : Finset.univ.image f = p.1.support.toFinset :=
    Finset.eq_of_subset_of_card_le hsubImage (by omega)
  let I : Finset (Fin 5) := Finset.univ.filter (fun i ↦ f i ∈ T)
  have hTI : T = I.image f := by
    ext v
    constructor
    · intro hv
      have hvImage : v ∈ Finset.univ.image f := by
        rw [himage]
        exact hTsub hv
      obtain ⟨i, _, hfi⟩ := Finset.mem_image.mp hvImage
      exact Finset.mem_image.mpr ⟨i,
        Finset.mem_filter.mpr ⟨Finset.mem_univ _, hfi ▸ hv⟩, hfi⟩
    · intro hv
      obtain ⟨i, hi, hfi⟩ := Finset.mem_image.mp hv
      exact hfi ▸ (Finset.mem_filter.mp hi).2
  have hIcard : 3 ≤ I.card := by
    have hc : T.card = I.card := by
      rw [hTI, Finset.card_image_of_injective _ hf]
    omega
  obtain ⟨i, hi, hinext⟩ := fin5_three_contains_cycle_neighbors I hIcard
  exact ⟨i, (Finset.mem_filter.mp hi).2,
    (Finset.mem_filter.mp hinext).2⟩

/-- The boundary-color pigeonhole step can be rerun after any legal
omitted-edge shift: an unsaturated color leaves two consecutive vertices
of the underlying five-cycle. -/
theorem FivePathState.adjacent_external_vertices_of_not_two_internal
    {F : Finset G.E} {k d : ℕ} {a b c : Fin k}
    (s : G.FivePathState F k a b)
    (hcritical : G.IsColorCriticalOn F k)
    (hdk : d + 1 < k) (hdegree : ∀ z, G.degreeOn F z ≤ d)
    (hthreshold : 7 * d < 6 * k + 2)
    (hnot : FivePathState.NotTwoInternalColor G s c) :
    ∃ i : Fin 5,
      FivePathState.HasExternalColorAt G s c (s.path.1.getVert i.val) ∧
      FivePathState.HasExternalColorAt G s c
        (s.path.1.getVert (i + 1).val) := by
  have hpresent := FivePathState.present_at_every_vertex_of_not_two_internal
    G s hcritical hdk hdegree hthreshold hnot
  have hpCard : s.path.1.support.toFinset.card = 5 := by
    rw [List.toFinset_card_of_nodup s.path.property.support_nodup,
      s.path.1.length_support, s.path_len]
  obtain ⟨T, hTsub, hTcard, hText⟩ :=
    G.three_external_vertices_of_present_unsaturated_color hpCard
      (by intro v hv; exact hpresent v (by simpa using hv)) hnot
  obtain ⟨i, hi, hinext⟩ :=
    G.fivePath_three_vertices_have_cycle_neighbor_pair_unoriented
      s.path s.path_len T hTsub hTcard
  exact ⟨i, hText _ hi, hText _ hinext⟩

/-- Boundary edges at both omitted-edge endpoints force their color to
differ from both missing endpoint colors. -/
theorem FivePathState.external_endpoint_color_ne_missing
    {F : Finset G.E} {k : ℕ} {a b c : Fin k}
    (s : G.FivePathState F k a b)
    (hleft : FivePathState.HasExternalColorAt G s c s.left)
    (hright : FivePathState.HasExternalColorAt G s c s.right) :
    c ≠ a ∧ c ≠ b := by
  obtain ⟨g, hgF, hgL, hgc, _⟩ := hleft
  obtain ⟨r, hrF, hrR, hrc, _⟩ := hright
  constructor
  · intro h
    exact (G.color_ne_of_mem_missingColorsAt
      (F.erase s.omitted) s.paint s.left a s.left_missing hgF hgL)
      (hgc.trans h)
  · intro h
    exact (G.color_ne_of_mem_missingColorsAt
      (F.erase s.omitted) s.paint s.right b s.right_missing hrF hrR)
      (hrc.trans h)

/-- The two normalized endpoint boundary edges are different. -/
theorem FivePathState.external_endpoint_edges_distinct
    {F : Finset G.E} {k : ℕ} {a b c : Fin k}
    (s : G.FivePathState F k a b)
    (hleft : FivePathState.HasExternalColorAt G s c s.left)
    (hright : FivePathState.HasExternalColorAt G s c s.right) :
    ∃ g r, g ≠ r ∧
      g ∈ F.erase s.omitted ∧ r ∈ F.erase s.omitted ∧
      G.Inc s.left g ∧ G.Inc s.right r ∧
      s.paint g = c ∧ s.paint r = c ∧
      g ∉ G.internalEdges (F.erase s.omitted)
        s.path.1.support.toFinset ∧
      r ∉ G.internalEdges (F.erase s.omitted)
        s.path.1.support.toFinset := by
  obtain ⟨g, hgF, hgL, hgc, hgExt⟩ := hleft
  obtain ⟨r, hrF, hrR, hrc, hrExt⟩ := hright
  have hgr : g ≠ r := by
    intro h
    have hends := G.endpoint_eq_or_endpoint_eq_swap_of_inc
      s.left_ne_right hgL (h ▸ hrR)
    have hL : s.left ∈ s.path.1.support.toFinset := by
      simpa only [List.mem_toFinset] using s.path.1.start_mem_support
    have hR : s.right ∈ s.path.1.support.toFinset := by
      simpa only [List.mem_toFinset] using s.path.1.end_mem_support
    apply hgExt
    simp only [internalEdges, Finset.mem_filter]
    rcases hends with ⟨hf, hs⟩ | ⟨hf, hs⟩
    · exact ⟨hgF, hf.symm ▸ hL, hs.symm ▸ hR⟩
    · exact ⟨hgF, hf.symm ▸ hR, hs.symm ▸ hL⟩
  exact ⟨g, r, hgr, hgF, hrF, hgL, hrR, hgc, hrc, hgExt, hrExt⟩

/-- An edge that leaves the path at a path vertex has an endpoint outside
the path. -/
theorem FivePathState.outside_neighbor_of_external_edge
    {F : Finset G.E} {k : ℕ} {a b : Fin k}
    (s : G.FivePathState F k a b)
    {v : G.V} (hv : v ∈ s.path.1.support.toFinset)
    {g : G.E} (hgF : g ∈ F.erase s.omitted)
    (hgExt : g ∉ G.internalEdges (F.erase s.omitted)
      s.path.1.support.toFinset) :
    ∃ w, G.Inc w g ∧ w ∉ s.path.1.support.toFinset ∧ w ≠ v := by
  by_cases hf : G.fst g ∈ s.path.1.support.toFinset
  · have hs : G.snd g ∉ s.path.1.support.toFinset := by
      intro hs
      exact hgExt (Finset.mem_filter.mpr ⟨hgF, hf, hs⟩)
    exact ⟨G.snd g, Or.inr rfl, hs, by intro h; exact hs (h ▸ hv)⟩
  · exact ⟨G.fst g, Or.inl rfl, hf,
      by intro h; exact hf (h ▸ hv)⟩

/-- The two exterior vertices reached by a normalized present color are
distinct, since equal-color edges at one vertex would violate propriety. -/
theorem FivePathState.distinct_outside_neighbors_of_external_endpoints
    {F : Finset G.E} {k : ℕ} {a b c : Fin k}
    (s : G.FivePathState F k a b)
    (hleft : FivePathState.HasExternalColorAt G s c s.left)
    (hright : FivePathState.HasExternalColorAt G s c s.right) :
    ∃ u w, u ≠ w ∧
      u ∉ s.path.1.support.toFinset ∧
      w ∉ s.path.1.support.toFinset ∧
      ∃ g r, g ∈ F.erase s.omitted ∧ r ∈ F.erase s.omitted ∧
        G.Inc s.left g ∧ G.Inc u g ∧
        G.Inc s.right r ∧ G.Inc w r ∧
        s.paint g = c ∧ s.paint r = c := by
  obtain ⟨g, r, hgr, hgF, hrF, hgL, hrR, hgc, hrc, hgExt, hrExt⟩ :=
    FivePathState.external_endpoint_edges_distinct G s hleft hright
  have hL : s.left ∈ s.path.1.support.toFinset := by
    simpa only [List.mem_toFinset] using s.path.1.start_mem_support
  have hR : s.right ∈ s.path.1.support.toFinset := by
    simpa only [List.mem_toFinset] using s.path.1.end_mem_support
  obtain ⟨u, hgu, huOut, _⟩ :=
    FivePathState.outside_neighbor_of_external_edge G s hL hgF hgExt
  obtain ⟨w, hrw, hwOut, _⟩ :=
    FivePathState.outside_neighbor_of_external_edge G s hR hrF hrExt
  have huw : u ≠ w := by
    intro h
    have heq : g = r := s.proper u
      (Finset.mem_coe.mpr (Finset.mem_filter.mpr ⟨hgF, hgu⟩))
      (Finset.mem_coe.mpr (Finset.mem_filter.mpr ⟨hrF, h ▸ hrw⟩))
      (hgc.trans hrc.symm)
    exact hgr heq
  exact ⟨u, w, huw, huOut, hwOut,
    g, r, hgF, hrF, hgL, hgu, hrR, hrw, hgc, hrc⟩

/-- Endpoint normalization may be repeated from any five-path state,
including states obtained by earlier omitted-edge shifts. -/
theorem FivePathState.exists_present_external_endpoint_state
    {F : Finset G.E} {k d : ℕ} {a b c : Fin k}
    (s : G.FivePathState F k a b)
    (hcritical : G.IsColorCriticalOn F k)
    (hdk : d + 1 < k) (hdegree : ∀ z, G.degreeOn F z ≤ d)
    (hthreshold : 7 * d < 6 * k + 2)
    (hnot : FivePathState.NotTwoInternalColor G s c) :
    ∃ a' b' : Fin k, ∃ t : G.FivePathState F k a' b',
      t.path.1.support.toFinset = s.path.1.support.toFinset ∧
      FivePathState.HasExternalColorAt G t c t.left ∧
      FivePathState.HasExternalColorAt G t c t.right ∧
      FivePathState.NotTwoInternalColor G t c ∧
      ∀ v ∈ t.path.1.support,
        c ∉ G.missingColorsAt (F.erase t.omitted) t.paint v := by
  have hpresent := FivePathState.present_at_every_vertex_of_not_two_internal
    G s hcritical hdk hdegree hthreshold hnot
  have hcneA : c ≠ a := by
    intro h
    exact hpresent s.left s.path.1.start_mem_support
      (by simpa [h] using s.left_missing)
  have hcneB : c ≠ b := by
    intro h
    exact hpresent s.right s.path.1.end_mem_support
      (by simpa [h] using s.right_missing)
  obtain ⟨i, hi, hinext⟩ :=
    FivePathState.adjacent_external_vertices_of_not_two_internal
      G s hcritical hdk hdegree hthreshold hnot
  have hp4 : s.path.1.getVert 4 = s.right := by
    simpa [s.path_len] using s.path.1.getVert_length
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
      exact ⟨by simpa using hi, by simpa using hinext⟩
    · right; right; left
      exact ⟨by simpa using hi, by simpa using hinext⟩
    · right; right; right; left
      exact ⟨by simpa using hi, by simpa using hinext⟩
    · right; right; right; right
      exact ⟨by simpa using hi, by simpa [hp4] using hinext⟩
    · left
      exact ⟨by simpa using hinext, by simpa [hp4] using hi⟩
  obtain ⟨a', b', t, hsupport, hleft, hright, hnotT⟩ :=
    FivePathState.exists_external_endpoint_state_of_cycle_pair
      G s hcritical hcneA hcneB hnot hpair
  exact ⟨a', b', t, hsupport, hleft, hright, hnotT,
    FivePathState.present_at_every_vertex_of_not_two_internal G t
      hcritical hdk hdegree hthreshold hnotT⟩

end WeightedEdgeColoring.WeightedMultigraph
