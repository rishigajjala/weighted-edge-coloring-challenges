import WeightedEdgeColoring.SubtwoOrdinaryFivePresentCircuitContradiction

/-!
# Ordered first return of the right component to the five-path
-/

namespace WeightedEdgeColoring.WeightedMultigraph

universe u
variable (G : WeightedMultigraph.{u})

theorem FivePathState.internal_vertex_ne_endpoints
    {F : Finset G.E} {k : ℕ} {a b : Fin k}
    (s : G.FivePathState F k a b) {j : ℕ}
    (hj0 : 0 < j) (hj4 : j < 4) :
    s.path.1.getVert j ≠ s.left ∧
      s.path.1.getVert j ≠ s.right := by
  have hlen := s.path_len
  constructor
  · intro h
    have hidx := s.path.property.getVert_injOn
      (Set.mem_Iic.mpr (by omega : j ≤ s.path.1.length))
      (Set.mem_Iic.mpr (by omega : 0 ≤ s.path.1.length))
      (by simpa using h)
    omega
  · intro h
    have hlast : s.path.1.getVert 4 = s.right := by
      simpa [hlen] using s.path.1.getVert_length
    have hidx := s.path.property.getVert_injOn
      (Set.mem_Iic.mpr (by omega : j ≤ s.path.1.length))
      (Set.mem_Iic.mpr (by omega : 4 ≤ s.path.1.length))
      (h.trans hlast.symm)
    omega

/-- The first step of a right-originating `(b,c)` path follows the
external `c` edge at `Y`, so it immediately leaves the old five-path. -/
theorem FivePathState.right_bc_path_first_vertex_outside
    {F : Finset G.E} {k : ℕ} {a b c : Fin k}
    (s : G.FivePathState F k a b)
    (hright : FivePathState.HasExternalColorAt G s c s.right)
    (p : (G.twoColorGraph (F.erase s.omitted) s.paint b c).Path
      s.right s.left) :
    p.1.getVert 1 ∉ s.path.1.support.toFinset := by
  have hpLen : 0 < p.1.length := by
    by_contra h
    have hz : p.1.length = 0 := by omega
    exact s.left_ne_right.symm (SimpleGraph.Walk.eq_of_length_eq_zero hz)
  have hadj : (G.twoColorGraph (F.erase s.omitted) s.paint b c).Adj
      s.right (p.1.getVert 1) := by
    simpa using p.1.adj_getVert_succ (i := 0) hpLen
  obtain ⟨r, hrF, hrR, hr1, hrColor⟩ :=
    G.exists_twoColorWitnessEdge (F.erase s.omitted) s.paint b c hadj
  have hrNeB : s.paint r ≠ b :=
    G.color_ne_of_mem_missingColorsAt
      (F.erase s.omitted) s.paint s.right b s.right_missing hrF hrR
  have hrC : s.paint r = c := hrColor.resolve_left hrNeB
  obtain ⟨g, hgF, hgR, hgC, hgExt⟩ := hright
  have hrg : r = g := by
    apply s.proper s.right
    · exact Finset.mem_coe.mpr (Finset.mem_filter.mpr ⟨hrF, hrR⟩)
    · exact Finset.mem_coe.mpr (Finset.mem_filter.mpr ⟨hgF, hgR⟩)
    · exact hrC.trans hgC.symm
  have hRmem : s.right ∈ s.path.1.support.toFinset := by
    simpa only [List.mem_toFinset] using s.path.1.end_mem_support
  obtain ⟨w, hgw, hwOut, hwNeR⟩ :=
    FivePathState.outside_neighbor_of_external_edge G s hRmem hgF hgExt
  have hPother := G.kempeOtherEndpoint_eq_of_incident
    hrR hr1 hadj.ne
  have hGother := G.kempeOtherEndpoint_eq_of_incident
    hgR hgw hwNeR.symm
  rw [hrg] at hPother
  have hPw : p.1.getVert 1 = w := hPother.symm.trans hGother
  exact hPw ▸ hwOut

/-- The first return of a simple right-to-left component path to the
five-path is a well-defined positive index. If that return is at the
left endpoint, no internal vertex of the five-path occurred on the
component path. -/
theorem FivePathState.ordered_first_return_to_fivePath
    {F : Finset G.E} {k : ℕ} {a b c : Fin k}
    (s : G.FivePathState F k a b)
    (p : (G.twoColorGraph (F.erase s.omitted) s.paint b c).Path
      s.right s.left) :
    ∃ i : ℕ, 0 < i ∧ i ≤ p.1.length ∧
      p.1.getVert i ∈ s.path.1.support.toFinset ∧
      (∀ j, 0 < j → j < i →
        p.1.getVert j ∉ s.path.1.support.toFinset) ∧
      (p.1.getVert i = s.left →
        s.path.1.getVert 1 ∉ p.1.support ∧
        s.path.1.getVert 2 ∉ p.1.support) := by
  classical
  let S := s.path.1.support.toFinset
  let P : ℕ → Prop := fun i ↦
    0 < i ∧ i ≤ p.1.length ∧ p.1.getVert i ∈ S
  have hpLen : 0 < p.1.length := by
    by_contra h
    have hz : p.1.length = 0 := by omega
    exact s.left_ne_right.symm (SimpleGraph.Walk.eq_of_length_eq_zero hz)
  have hLmem : s.left ∈ S := by
    simpa [S] using s.path.1.start_mem_support
  have hP : ∃ i, P i := by
    refine ⟨p.1.length, hpLen, le_refl _, ?_⟩
    simpa only [p.1.getVert_length] using hLmem
  let i := Nat.find hP
  have hi : P i := Nat.find_spec hP
  refine ⟨i, hi.1, hi.2.1, hi.2.2, ?_, ?_⟩
  · intro j hj0 hji hjS
    exact (Nat.find_min hP hji) ⟨hj0, by omega, hjS⟩
  · intro hiL
    have hiEnd : i = p.1.length := by
      apply p.property.getVert_injOn
        (Set.mem_Iic.mpr hi.2.1)
        (Set.mem_Iic.mpr (le_refl _))
      simpa only [p.1.getVert_length] using hiL
    constructor
    · intro hZ1
      obtain ⟨j, hj, hjLe⟩ :=
        SimpleGraph.Walk.mem_support_iff_exists_getVert.mp hZ1
      have hZ1neR :=
        (FivePathState.internal_vertex_ne_endpoints G s
          (by omega : 0 < 1) (by omega : 1 < 4)).2
      have hZ1neL :=
        (FivePathState.internal_vertex_ne_endpoints G s
          (by omega : 0 < 1) (by omega : 1 < 4)).1
      have hj0 : 0 < j := by
        by_contra h
        have hz : j = 0 := by omega
        exact hZ1neR (hj.symm.trans (by simpa [hz] using p.1.getVert_zero))
      have hjEnd : j < p.1.length := by
        have hne : j ≠ p.1.length := by
          intro h
          exact hZ1neL (hj.symm.trans (by simpa [h] using p.1.getVert_length))
        omega
      have hmem : p.1.getVert j ∈ S := by
        rw [hj]
        simpa [S] using s.path.1.getVert_mem_support 1
      exact (Nat.find_min hP (by omega : j < i))
        ⟨hj0, hjLe, hmem⟩
    · intro hZ2
      obtain ⟨j, hj, hjLe⟩ :=
        SimpleGraph.Walk.mem_support_iff_exists_getVert.mp hZ2
      have hZ2neR :=
        (FivePathState.internal_vertex_ne_endpoints G s
          (by omega : 0 < 2) (by omega : 2 < 4)).2
      have hZ2neL :=
        (FivePathState.internal_vertex_ne_endpoints G s
          (by omega : 0 < 2) (by omega : 2 < 4)).1
      have hj0 : 0 < j := by
        by_contra h
        have hz : j = 0 := by omega
        exact hZ2neR (hj.symm.trans (by simpa [hz] using p.1.getVert_zero))
      have hjEnd : j < p.1.length := by
        have hne : j ≠ p.1.length := by
          intro h
          exact hZ2neL (hj.symm.trans (by simpa [h] using p.1.getVert_length))
        omega
      have hmem : p.1.getVert j ∈ S := by
        rw [hj]
        simpa [S] using s.path.1.getVert_mem_support 2
      exact (Nat.find_min hP (by omega : j < i))
        ⟨hj0, hjLe, hmem⟩

/-- A first return at `X` is impossible in Andersen's present-color
case, with avoidance derived from the least return index. -/
theorem FivePathState.ordered_first_return_not_left
    {F : Finset G.E} {k d : ℕ} {a b c : Fin k}
    (s : G.FivePathState F k a b)
    (hcritical : G.IsColorCriticalOn F k)
    (hdk : d + 1 < k) (hdegree : ∀ z, G.degreeOn F z ≤ d)
    (hthreshold : 7 * d < 6 * k + 2)
    (hleft : FivePathState.HasExternalColorAt G s c s.left)
    (hright : FivePathState.HasExternalColorAt G s c s.right)
    (p : (G.twoColorGraph (F.erase s.omitted) s.paint b c).Path
      s.right s.left) :
    ∃ i : ℕ, 0 < i ∧ i ≤ p.1.length ∧
      p.1.getVert i ∈ s.path.1.support.toFinset ∧
      (∀ j, 0 < j → j < i →
        p.1.getVert j ∉ s.path.1.support.toFinset) ∧
      p.1.getVert i ≠ s.left := by
  obtain ⟨i, hi0, hiLe, hiMem, hiFirst, hiAvoid⟩ :=
    FivePathState.ordered_first_return_to_fivePath G s p
  refine ⟨i, hi0, hiLe, hiMem, hiFirst, ?_⟩
  intro hiL
  obtain ⟨hZ1, hZ2⟩ := hiAvoid hiL
  exact FivePathState.first_hit_left_circuit_impossible G s
    hcritical hdk hdegree hthreshold hleft hright p hZ1 hZ2

/-- The first return therefore lands at one of the three internal
vertices. This is the exact case split left after the circuit case is
eliminated. -/
theorem FivePathState.ordered_first_return_internal
    {F : Finset G.E} {k d : ℕ} {a b c : Fin k}
    (s : G.FivePathState F k a b)
    (hcritical : G.IsColorCriticalOn F k)
    (hdk : d + 1 < k) (hdegree : ∀ z, G.degreeOn F z ≤ d)
    (hthreshold : 7 * d < 6 * k + 2)
    (hleft : FivePathState.HasExternalColorAt G s c s.left)
    (hright : FivePathState.HasExternalColorAt G s c s.right)
    (p : (G.twoColorGraph (F.erase s.omitted) s.paint b c).Path
      s.right s.left) :
    ∃ i : ℕ, 1 < i ∧ i ≤ p.1.length ∧
      (∀ j, 0 < j → j < i →
        p.1.getVert j ∉ s.path.1.support.toFinset) ∧
      (p.1.getVert i = s.path.1.getVert 1 ∨
        p.1.getVert i = s.path.1.getVert 2 ∨
        p.1.getVert i = s.path.1.getVert 3) := by
  obtain ⟨i, hi0, hiLe, hiMem, hiFirst, hiNeL⟩ :=
    FivePathState.ordered_first_return_not_left G s
      hcritical hdk hdegree hthreshold hleft hright p
  have hiGt1 : 1 < i := by
    have hfirstOut :=
      FivePathState.right_bc_path_first_vertex_outside G s hright p
    by_contra h
    have hi1 : i = 1 := by omega
    exact hfirstOut (by simpa [hi1] using hiMem)
  refine ⟨i, hiGt1, hiLe, hiFirst, ?_⟩
  have hiNeR : p.1.getVert i ≠ s.right := by
    intro h
    have hidx := p.property.getVert_injOn
      (Set.mem_Iic.mpr hiLe)
      (Set.mem_Iic.mpr (by omega : 0 ≤ p.1.length))
      (by simpa using h)
    omega
  obtain ⟨j, hj, hjLe⟩ :=
    SimpleGraph.Walk.mem_support_iff_exists_getVert.mp
      (by simpa only [List.mem_toFinset] using hiMem)
  have hj4 : j ≤ 4 := by have := s.path_len; omega
  interval_cases j
  · exact False.elim (hiNeL (by simpa using hj.symm))
  · exact Or.inl hj.symm
  · exact Or.inr (Or.inl hj.symm)
  · exact Or.inr (Or.inr hj.symm)
  · exact False.elim (hiNeR (by
      have hlast : s.path.1.getVert 4 = s.right := by
        simpa [s.path_len] using s.path.1.getVert_length
      simpa [hlast] using hj.symm))

/-- The connected right/left `(b,c)` case has an ordered first return
at one of the three internal five-path vertices. No path witness or
avoidance condition is required from the caller. -/
theorem FivePathState.same_component_first_return_internal
    {F : Finset G.E} {k d : ℕ} {a b c : Fin k}
    (s : G.FivePathState F k a b)
    (hcritical : G.IsColorCriticalOn F k)
    (hdk : d + 1 < k) (hdegree : ∀ z, G.degreeOn F z ≤ d)
    (hthreshold : 7 * d < 6 * k + 2)
    (hleft : FivePathState.HasExternalColorAt G s c s.left)
    (hright : FivePathState.HasExternalColorAt G s c s.right)
    (hcomp : (G.twoColorGraph (F.erase s.omitted) s.paint b c).connectedComponentMk
        s.right =
      (G.twoColorGraph (F.erase s.omitted) s.paint b c).connectedComponentMk
        s.left) :
    ∃ p : (G.twoColorGraph (F.erase s.omitted) s.paint b c).Path
      s.right s.left,
      ∃ i : ℕ, 1 < i ∧ i ≤ p.1.length ∧
        (∀ j, 0 < j → j < i →
          p.1.getVert j ∉ s.path.1.support.toFinset) ∧
        (p.1.getVert i = s.path.1.getVert 1 ∨
          p.1.getVert i = s.path.1.getVert 2 ∨
          p.1.getVert i = s.path.1.getVert 3) := by
  have hreach : (G.twoColorGraph (F.erase s.omitted) s.paint b c).Reachable
      s.right s.left := SimpleGraph.ConnectedComponent.exact hcomp
  obtain ⟨walk⟩ := hreach
  let p := walk.toPath
  obtain ⟨i, hi0, hiLe, hiFirst, hiCase⟩ :=
    FivePathState.ordered_first_return_internal G s hcritical
      hdk hdegree hthreshold hleft hright p
  exact ⟨p, i, hi0, hiLe, hiFirst, hiCase⟩

end WeightedEdgeColoring.WeightedMultigraph
