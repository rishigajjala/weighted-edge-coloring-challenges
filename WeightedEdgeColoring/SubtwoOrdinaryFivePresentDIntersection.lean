import WeightedEdgeColoring.SubtwoOrdinaryFivePresentVZ1ForcedEdge

/-!
# An edge internal to both critical five-path supports
-/

namespace WeightedEdgeColoring.WeightedMultigraph

universe u
variable (G : WeightedMultigraph.{u})

/-- If the only common vertices of two supports are `X`, `Y`, and `Z₁`,
then an edge at `Y` internal to both supports, but not at `X`, joins
`Y` to `Z₁`. -/
theorem internal_edge_in_two_supports_at_right
    {F : Finset G.E} {S T : Finset G.V} {x y z : G.V}
    (hinter : ∀ v, v ∈ S → v ∈ T → v = x ∨ v = y ∨ v = z)
    {g : G.E}
    (hgS : g ∈ G.internalEdges F S)
    (hgT : g ∈ G.internalEdges F T)
    (hgY : G.Inc y g)
    (hgNotX : ¬G.Inc x g) :
    G.Inc z g := by
  simp only [internalEdges, Finset.mem_filter] at hgS hgT
  rcases hgY with hyF | hyS
  · have hother := hinter (G.snd g) hgS.2.2 hgT.2.2
    rcases hother with hx | hy | hz
    · exact False.elim (hgNotX (Or.inr hx))
    · exact False.elim (G.noLoop g (hyF.trans hy.symm))
    · exact Or.inr hz
  · have hother := hinter (G.fst g) hgS.2.1 hgT.2.1
    rcases hother with hx | hy | hz
    · exact False.elim (hgNotX (Or.inl hx))
    · exact False.elim (G.noLoop g (hy.trans hyS.symm))
    · exact Or.inl hz

/-- Five specified distinct vertices exhaust any simple path whose
support has at most five vertices. -/
theorem five_path_support_eq_of_five_members
    {H : SimpleGraph G.V} {x y z w u : G.V}
    (q : H.Path x y) (hqCard : q.1.support.toFinset.card ≤ 5)
    (hz : z ∈ q.1.support) (hw : w ∈ q.1.support)
    (hu : u ∈ q.1.support)
    (hxz : x ≠ z) (hxy : x ≠ y) (hzy : z ≠ y)
    (hwx : w ≠ x) (hwz : w ≠ z) (hwy : w ≠ y)
    (hux : u ≠ x) (huz : u ≠ z) (huy : u ≠ y)
    (hwu : w ≠ u) :
    q.1.support.toFinset = {x,z,w,u,y} := by
  have hsub : ({x,z,w,u,y} : Finset G.V) ⊆
      q.1.support.toFinset := by
    intro v hv
    simp only [Finset.mem_insert, Finset.mem_singleton] at hv
    rcases hv with rfl | rfl | rfl | rfl | rfl
    · simpa only [List.mem_toFinset] using q.1.start_mem_support
    · simpa only [List.mem_toFinset] using hz
    · simpa only [List.mem_toFinset] using hw
    · simpa only [List.mem_toFinset] using hu
    · simpa only [List.mem_toFinset] using q.1.end_mem_support
  have hnodup : [x,z,w,u,y].Nodup := by
    simp [hxz, hxy, hzy, hwx.symm, hwz.symm, hwy, hux.symm,
      huz.symm, huy, hwu]
  have heq : ([x,z,w,u,y] : List G.V).toFinset =
      ({x,z,w,u,y} : Finset G.V) := by
    ext v
    simp
  have hcard : ({x,z,w,u,y} : Finset G.V).card = 5 := by
    rw [← heq, List.toFinset_card_of_nodup hnodup]
    simp
  exact (Finset.eq_of_subset_of_card_le hsub (by omega)).symm

/-- The old support and a new five-vertex critical path can meet only
at `X`, `Z₁`, and `Y` when its two remaining vertices lie outside. -/
theorem old_new_five_support_intersection
    {H : SimpleGraph G.V} {x y z w u : G.V}
    {S : Finset G.V} (hwOut : w ∉ S) (huOut : u ∉ S)
    (q : H.Path x y) (hq : q.1.support.toFinset = {x,z,w,u,y}) :
    ∀ v, v ∈ S → v ∈ q.1.support.toFinset →
      v = x ∨ v = y ∨ v = z := by
  intro v hvS hvQ
  rw [hq] at hvQ
  simp only [Finset.mem_insert, Finset.mem_singleton] at hvQ
  rcases hvQ with hx | hz | hw | hu | hy
  · exact Or.inl hx
  · exact Or.inr (Or.inr hz)
  · exact False.elim (hwOut (hw ▸ hvS))
  · exact False.elim (huOut (hu ▸ hvS))
  · exact Or.inr (Or.inl hy)

/-- A color absent at the left endpoint cannot leave a critical
five-path from its right endpoint, regardless of the stored
orientation of the omitted edge. -/
theorem FivePathState.right_color_edge_internal_of_missing_left
    {F : Finset G.E} {k d : ℕ} {a b c : Fin k}
    (s : G.FivePathState F k a b)
    (hcritical : G.IsColorCriticalOn F k)
    (hdk : d + 1 < k) (hdegree : ∀ z, G.degreeOn F z ≤ d)
    (hthreshold : 7 * d < 6 * k + 2)
    (hcX : c ∈ G.missingColorsAt (F.erase s.omitted) s.paint s.left)
    {g : G.E} (hgF : g ∈ F.erase s.omitted)
    (hgY : G.Inc s.right g) (hgC : s.paint g = c) :
    g ∈ G.internalEdges (F.erase s.omitted)
      s.path.1.support.toFinset := by
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
    have hv0 : G.snd s.omitted ∈ p0.1.support := by
      rw [hpSupport, hsnd]
      exact s.path.1.end_mem_support
    have hg0 := G.endpointMissingColor_edge_incident_fivePath_internal
      (v := G.snd s.omitted)
      hcritical s.omitted_mem s.proper ha0 hb0 p0 hpLen
      hdk hdegree hthreshold
      hv0
      hgF (by simpa [hsnd] using hgY)
      (Finset.mem_union.mpr (Or.inl (hgC ▸ hc0)))
    simpa only [hpSupport] using hg0
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
    have hdegreeR : ∀ z, R.degreeOn F z ≤ d := by
      intro z
      simpa [R] using hdegree z
    have haR : a ∈ R.missingColorsAt (F.erase s.omitted)
        s.paint (R.fst s.omitted) := by simpa [R, hRf] using s.left_missing
    have hbR : b ∈ R.missingColorsAt (F.erase s.omitted)
        s.paint (R.snd s.omitted) := by simpa [R, hRs] using s.right_missing
    have hcR : c ∈ R.missingColorsAt (F.erase s.omitted)
        s.paint (R.fst s.omitted) := by simpa [R, hRf] using hcX
    have hgR : R.Inc s.right g := by simpa [R] using hgY
    have hvR : R.snd s.omitted ∈ pR.1.support := by
      rw [hpRSupport, hRs]
      exact s.path.1.end_mem_support
    have hgInternal := R.endpointMissingColor_edge_incident_fivePath_internal
      (v := R.snd s.omitted)
      hcriticalR s.omitted_mem hproperR haR hbR pR hpRLen
      hdk hdegreeR hthreshold
      hvR
      hgF (by simpa [hRs] using hgR)
      (Finset.mem_union.mpr (Or.inl (hgC ▸ hcR)))
    simpa [R, hpRSupport] using hgInternal

/-- Enumerating the support of the four-edge normalized path. -/
theorem FivePathState.support_eq_five_vertices
    {F : Finset G.E} {k : ℕ} {a b : Fin k}
    (s : G.FivePathState F k a b) :
    s.path.1.support.toFinset =
      {s.left, s.path.1.getVert 1, s.path.1.getVert 2,
        s.path.1.getVert 3, s.right} := by
  ext v
  constructor
  · intro hv
    obtain ⟨i, hi, hiLe⟩ :=
      SimpleGraph.Walk.mem_support_iff_exists_getVert.mp
        (List.mem_toFinset.mp hv)
    have hi4 : i ≤ 4 := by have := s.path_len; omega
    simp only [Finset.mem_insert, Finset.mem_singleton]
    interval_cases i
    · exact Or.inl (hi.symm.trans s.path.1.getVert_zero)
    · exact Or.inr (Or.inl hi.symm)
    · exact Or.inr (Or.inr (Or.inl hi.symm))
    · exact Or.inr (Or.inr (Or.inr (Or.inl hi.symm)))
    · apply Or.inr
      apply Or.inr
      apply Or.inr
      apply Or.inr
      have hend : s.path.1.getVert 4 = s.right := by
        simpa [s.path_len] using s.path.1.getVert_length
      exact hi.symm.trans hend
  · intro hv
    simp only [Finset.mem_insert, Finset.mem_singleton] at hv
    rcases hv with rfl | rfl | rfl | rfl | rfl
    · simpa only [List.mem_toFinset] using s.path.1.start_mem_support
    · simpa only [List.mem_toFinset] using s.path.1.getVert_mem_support 1
    · simpa only [List.mem_toFinset] using s.path.1.getVert_mem_support 2
    · simpa only [List.mem_toFinset] using s.path.1.getVert_mem_support 3
    · simpa only [List.mem_toFinset] using s.path.1.end_mem_support

end WeightedEdgeColoring.WeightedMultigraph
