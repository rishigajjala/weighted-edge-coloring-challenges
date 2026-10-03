import WeightedEdgeColoring.SubtwoOrdinaryFivePresentRootedPathOrder

/-!
# Ordered Y-rooted paths to the middle pair
-/

namespace WeightedEdgeColoring.WeightedMultigraph

universe u
variable (G : WeightedMultigraph.{u})

noncomputable local instance middleOrderFiniteNeighborSet
    (H : SimpleGraph G.V) (v : G.V) : Fintype (H.neighborSet v) :=
  @Subtype.fintype G.V (fun w ↦ w ∈ H.neighborSet v)
    (Classical.decPred _) G.instFintypeV

/-- A Y→X path whose first old-path return is Z₁ has no middle
vertex in its support. -/
theorem FivePathState.first_return_z1_path_avoids_middle
    {F : Finset G.E} {k : ℕ} {a b c : Fin k}
    (s : G.FivePathState F k a b)
    (p : (G.twoColorGraph (F.erase s.omitted) s.paint b c).Path
      s.right s.left)
    {i : ℕ} (hi : 1 < i) (hiLe : i ≤ p.1.length)
    (hfirst : ∀ j, 0 < j → j < i →
      p.1.getVert j ∉ s.path.1.support.toFinset)
    (hiZ1 : p.1.getVert i = s.path.1.getVert 1) :
    s.path.1.getVert 2 ∉ p.1.support ∧
      s.path.1.getVert 3 ∉ p.1.support := by
  have hshape := FivePathState.first_return_at_z1_then_left
    G s p hi hiLe hfirst hiZ1
  have havoid (m : ℕ) (hm : m = 2 ∨ m = 3) :
      s.path.1.getVert m ∉ p.1.support := by
    intro hmem
    obtain ⟨j, hj, hjLe⟩ :=
      SimpleGraph.Walk.mem_support_iff_exists_getVert.mp hmem
    have hmidS : s.path.1.getVert m ∈ s.path.1.support.toFinset := by
      simpa only [List.mem_toFinset] using s.path.1.getVert_mem_support m
    have hlen : p.1.length = i + 1 := hshape.2.symm
    by_cases hj0 : j = 0
    · have hY : s.path.1.getVert m = s.right := by
        have hstart := p.1.getVert_zero
        exact hj.symm.trans (by simpa [hj0] using hstart)
      rcases hm with rfl | rfl
      · exact (FivePathState.internal_vertex_ne_endpoints G s
          (by omega : 0 < 2) (by omega : 2 < 4)).2 hY
      · exact (FivePathState.internal_vertex_ne_endpoints G s
          (by omega : 0 < 3) (by omega : 3 < 4)).2 hY
    by_cases hji : j = i
    · have hZ1 : s.path.1.getVert m = s.path.1.getVert 1 := by
        exact hj.symm.trans (by simpa [hji] using hiZ1)
      have hinj := s.path.property.getVert_injOn
        (Set.mem_Iic.mpr (by have := s.path_len; omega : m ≤ s.path.1.length))
        (Set.mem_Iic.mpr (by have := s.path_len; omega : 1 ≤ s.path.1.length))
        hZ1
      rcases hm with rfl | rfl <;> omega
    by_cases hjlast : j = i + 1
    · have hX : s.path.1.getVert m = s.left := by
        exact hj.symm.trans (by simpa [hjlast] using hshape.1)
      rcases hm with rfl | rfl
      · exact (FivePathState.internal_vertex_ne_endpoints G s
          (by omega : 0 < 2) (by omega : 2 < 4)).1 hX
      · exact (FivePathState.internal_vertex_ne_endpoints G s
          (by omega : 0 < 3) (by omega : 3 < 4)).1 hX
    have hjPos : 0 < j := by omega
    have hjLt : j < i := by omega
    exact hfirst j hjPos hjLt (hj ▸ hmidS)
  exact ⟨havoid 2 (Or.inl rfl), havoid 3 (Or.inr rfl)⟩

/-- Paths from `Y` to either middle vertex pass through `X`; the
two middle vertices are then ordered along the same degree-two chain. -/
theorem FivePathState.exists_ordered_middle_paths_after_left
    {F : Finset G.E} {k D : ℕ} {a b c : Fin k}
    (s : G.FivePathState F k a b)
    (hcritical : G.IsColorCriticalOn F k)
    (hdk : D + 1 < k) (hdegree : ∀ z, G.degreeOn F z ≤ D)
    (hthreshold : 7 * D < 6 * k + 2)
    (hnot : FivePathState.NotTwoInternalColor G s c)
    (hleft : FivePathState.HasExternalColorAt G s c s.left)
    (hright : FivePathState.HasExternalColorAt G s c s.right)
    (hZ1 : FivePathState.HasExternalColorAt G s c
      (s.path.1.getVert 1))
    (p : (G.twoColorGraph (F.erase s.omitted) s.paint b c).Path
      s.right s.left)
    {i : ℕ} (hi : 1 < i) (hiLe : i ≤ p.1.length)
    (hfirst : ∀ j, 0 < j → j < i →
      p.1.getVert j ∉ s.path.1.support.toFinset)
    (hiZ1 : p.1.getVert i = s.path.1.getVert 1)
    (hnoMiddle : ¬∃ g, g ∈ F.erase s.omitted ∧
      G.Inc (s.path.1.getVert 2) g ∧
      G.Inc (s.path.1.getVert 3) g ∧ s.paint g = c) :
    ∃ q₂ : (G.twoColorGraph (F.erase s.omitted) s.paint b c).Path
        s.right (s.path.1.getVert 2),
      ∃ q₃ : (G.twoColorGraph (F.erase s.omitted) s.paint b c).Path
          s.right (s.path.1.getVert 3),
        p.1.length ≤ q₂.1.length ∧
        p.1.length ≤ q₃.1.length ∧
        q₂.1.getVert p.1.length = s.left ∧
        q₃.1.getVert p.1.length = s.left ∧
        (s.path.1.getVert 2 ∈ q₃.1.support ∨
          s.path.1.getVert 3 ∈ q₂.1.support) := by
  let H := G.twoColorGraph (F.erase s.omitted) s.paint b c
  have hmax : ∀ v, H.degree v ≤ 2 := by
    intro v
    exact G.twoColorGraph_degree_le_two_of_isProperOn
      (F.erase s.omitted) s.paint s.proper b c v
  have hcYpresent : c ∉ G.missingColorsAt
      (F.erase s.omitted) s.paint s.right := by
    have hright' := hright
    obtain ⟨r,hrF,hrY,hrC,_⟩ := hright'
    intro hmiss
    exact (G.color_ne_of_mem_missingColorsAt
      (F.erase s.omitted) s.paint s.right c hmiss hrF hrY) hrC
  have hYactive : G.IsTwoColorActive
      (F.erase s.omitted) s.paint b c s.right :=
    Or.inl ⟨s.right_missing, hcYpresent⟩
  have hroot : H.degree s.right ≤ 1 :=
    G.twoColorGraph_degree_le_one_of_active
      (F.erase s.omitted) s.paint s.proper b c s.right hYactive
  obtain ⟨hZ2Comp,hZ3Comp⟩ :=
    FivePathState.middle_pair_in_right_bc_component_of_no_middle_c
      G s hcritical hdk hdegree hthreshold
      hnot hleft hright hZ1 p hnoMiddle
  have hreach2 : H.Reachable s.right (s.path.1.getVert 2) :=
    SimpleGraph.ConnectedComponent.exact hZ2Comp.symm
  have hreach3 : H.Reachable s.right (s.path.1.getVert 3) :=
    SimpleGraph.ConnectedComponent.exact hZ3Comp.symm
  obtain ⟨walk₂⟩ := hreach2
  obtain ⟨walk₃⟩ := hreach3
  let q₂ := walk₂.toPath
  let q₃ := walk₃.toPath
  obtain ⟨hZ2notP,hZ3notP⟩ :=
    FivePathState.first_return_z1_path_avoids_middle
      G s p hi hiLe hfirst hiZ1
  have hq₂Len : p.1.length ≤ q₂.1.length := by
    by_contra h
    have hqShort : q₂.1.length ≤ p.1.length := by omega
    have hsame := G.rooted_paths_agree_until_shorter_ends
      p q₂ hmax hroot q₂.1.length hqShort le_rfl
    have hqEnd : q₂.1.getVert q₂.1.length =
        s.path.1.getVert 2 := q₂.1.getVert_length
    have hmem : s.path.1.getVert 2 ∈ p.1.support := by
      have hpMem := p.1.getVert_mem_support q₂.1.length
      exact (hsame.trans hqEnd) ▸ hpMem
    exact hZ2notP hmem
  have hq₃Len : p.1.length ≤ q₃.1.length := by
    by_contra h
    have hqShort : q₃.1.length ≤ p.1.length := by omega
    have hsame := G.rooted_paths_agree_until_shorter_ends
      p q₃ hmax hroot q₃.1.length hqShort le_rfl
    have hqEnd : q₃.1.getVert q₃.1.length =
        s.path.1.getVert 3 := q₃.1.getVert_length
    have hmem : s.path.1.getVert 3 ∈ p.1.support := by
      have hpMem := p.1.getVert_mem_support q₃.1.length
      exact (hsame.trans hqEnd) ▸ hpMem
    exact hZ3notP hmem
  have hX₂ : q₂.1.getVert p.1.length = s.left := by
    have hsame := G.rooted_paths_agree_until_shorter_ends
      p q₂ hmax hroot p.1.length le_rfl hq₂Len
    exact hsame.symm.trans p.1.getVert_length
  have hX₃ : q₃.1.getVert p.1.length = s.left := by
    have hsame := G.rooted_paths_agree_until_shorter_ends
      p q₃ hmax hroot p.1.length le_rfl hq₃Len
    exact hsame.symm.trans p.1.getVert_length
  have hcomp := G.rooted_path_endpoints_comparable
    q₂ q₃ hmax hroot
  exact ⟨q₂,q₃,hq₂Len,hq₃Len,hX₂,hX₃,hcomp⟩

end WeightedEdgeColoring.WeightedMultigraph
