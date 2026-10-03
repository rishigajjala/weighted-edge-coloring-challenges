import WeightedEdgeColoring.SubtwoOrdinaryFivePresentMiddleComponent

/-!
# Prefix order of simple paths in a degree-two component
-/

namespace WeightedEdgeColoring.WeightedMultigraph

universe u
variable (G : WeightedMultigraph.{u})

noncomputable local instance rootedFiniteNeighborSet
    (H : SimpleGraph G.V) (v : G.V) : Fintype (H.neighborSet v) :=
  @Subtype.fintype G.V (fun w ↦ w ∈ H.neighborSet v)
    (Classical.decPred _) G.instFintypeV

/-- At a vertex of degree at most one, two adjacent vertices agree. -/
theorem unique_neighbor_of_degree_le_one
    {H : SimpleGraph G.V} {v w z : G.V}
    (hdegree : H.degree v ≤ 1)
    (hvw : H.Adj v w) (hvz : H.Adj v z) : w = z := by
  classical
  have hw : w ∈ H.neighborFinset v := (H.mem_neighborFinset _ _).mpr hvw
  have hz : z ∈ H.neighborFinset v := (H.mem_neighborFinset _ _).mpr hvz
  have hcard : (H.neighborFinset v).card ≤ 1 := by
    rw [H.card_neighborFinset_eq_degree]
    exact hdegree
  exact Finset.card_le_one.mp hcard w hw z hz

/-- At a vertex of degree at most two, two nonbacktracking next
neighbors after the same previous vertex agree. -/
theorem unique_nonbacktracking_neighbor_of_degree_le_two
    {H : SimpleGraph G.V} {v prev w z : G.V}
    (hdegree : H.degree v ≤ 2)
    (hprev : H.Adj v prev) (hw : H.Adj v w) (hz : H.Adj v z)
    (hwp : w ≠ prev) (hzp : z ≠ prev) : w = z := by
  classical
  have hpairCard : ({prev,w} : Finset G.V).card = 2 := by
    simp [hwp.symm]
  have hpairSub : ({prev,w} : Finset G.V) ⊆ H.neighborFinset v := by
    intro u hu
    simp only [Finset.mem_insert, Finset.mem_singleton] at hu
    rcases hu with rfl | rfl
    · exact (H.mem_neighborFinset _ _).mpr hprev
    · exact (H.mem_neighborFinset _ _).mpr hw
  have hcard : (H.neighborFinset v).card ≤ 2 := by
    rw [H.card_neighborFinset_eq_degree]
    exact hdegree
  have heq : ({prev,w} : Finset G.V) = H.neighborFinset v :=
    Finset.eq_of_subset_of_card_le hpairSub (by omega)
  have hzpair : z ∈ ({prev,w} : Finset G.V) := by
    rw [heq]
    exact (H.mem_neighborFinset _ _).mpr hz
  rcases Finset.mem_insert.mp hzpair with hzp' | hzw
  · exact False.elim (hzp hzp')
  · have hzw' : z = w := by simpa using hzw
    exact hzw'.symm

/-- Two simple paths from a degree-one root in a graph of maximum
degree two have the same vertices at all shared indices. -/
theorem rooted_paths_agree_until_shorter_ends
    {H : SimpleGraph G.V} {x y z : G.V}
    (p : H.Path x y) (q : H.Path x z)
    (hmax : ∀ v, H.degree v ≤ 2)
    (hroot : H.degree x ≤ 1) :
    ∀ i, i ≤ p.1.length → i ≤ q.1.length →
      p.1.getVert i = q.1.getVert i := by
  have hpair : ∀ i, i + 1 ≤ p.1.length → i + 1 ≤ q.1.length →
      p.1.getVert i = q.1.getVert i ∧
        p.1.getVert (i + 1) = q.1.getVert (i + 1) := by
    intro i
    induction i with
    | zero =>
      intro hp hq
      have h0 : p.1.getVert 0 = q.1.getVert 0 := by
        rw [p.1.getVert_zero, q.1.getVert_zero]
      have hpAdj : H.Adj x (p.1.getVert 1) := by
        simpa using p.1.adj_getVert_succ (i := 0) (by omega)
      have hqAdj : H.Adj x (q.1.getVert 1) := by
        simpa using q.1.adj_getVert_succ (i := 0) (by omega)
      exact ⟨h0, G.unique_neighbor_of_degree_le_one hroot hpAdj hqAdj⟩
    | succ j ih =>
      intro hp hq
      have hprev := ih (by omega) (by omega)
      have hpAdjPrev : H.Adj (p.1.getVert (j+1))
          (p.1.getVert j) := by
        exact (p.1.adj_getVert_succ (i := j) (by omega)).symm
      have hpAdjNext : H.Adj (p.1.getVert (j+1))
          (p.1.getVert (j+2)) := by
        exact p.1.adj_getVert_succ (i := j+1) (by omega)
      have hqAdjNext : H.Adj (p.1.getVert (j+1))
          (q.1.getVert (j+2)) := by
        simpa [hprev.2] using q.1.adj_getVert_succ
          (i := j+1) (by omega)
      have hpNonback : p.1.getVert (j+2) ≠ p.1.getVert j := by
        intro h
        have hinj := p.property.getVert_injOn
          (Set.mem_Iic.mpr (by omega : j+2 ≤ p.1.length))
          (Set.mem_Iic.mpr (by omega : j ≤ p.1.length)) h
        omega
      have hqNonback : q.1.getVert (j+2) ≠ p.1.getVert j := by
        intro h
        have h' : q.1.getVert (j+2) = q.1.getVert j :=
          h.trans hprev.1
        have hinj := q.property.getVert_injOn
          (Set.mem_Iic.mpr (by omega : j+2 ≤ q.1.length))
          (Set.mem_Iic.mpr (by omega : j ≤ q.1.length)) h'
        omega
      have hnext := G.unique_nonbacktracking_neighbor_of_degree_le_two
        (hmax (p.1.getVert (j+1))) hpAdjPrev hpAdjNext hqAdjNext
        hpNonback hqNonback
      exact ⟨hprev.2, by simpa [Nat.succ_eq_add_one] using hnext⟩
  intro i hp hq
  by_cases hi0 : i = 0
  · subst i
    rw [p.1.getVert_zero, q.1.getVert_zero]
  · have hi : 0 < i := Nat.pos_of_ne_zero hi0
    obtain ⟨j,rfl⟩ := Nat.exists_eq_succ_of_ne_zero hi0
    exact (hpair j (by omega) (by omega)).2

/-- Consequently, one rooted path's endpoint lies on the other
whenever the latter endpoint does not lie on the first path. -/
theorem rooted_path_endpoints_comparable
    {H : SimpleGraph G.V} {x y z : G.V}
    (p : H.Path x y) (q : H.Path x z)
    (hmax : ∀ v, H.degree v ≤ 2)
    (hroot : H.degree x ≤ 1) :
    y ∈ q.1.support ∨ z ∈ p.1.support := by
  by_cases hlen : p.1.length ≤ q.1.length
  · left
    have hsame := G.rooted_paths_agree_until_shorter_ends
      p q hmax hroot p.1.length le_rfl hlen
    have hend : p.1.getVert p.1.length = y := p.1.getVert_length
    have hqmem : q.1.getVert p.1.length ∈ q.1.support :=
      q.1.getVert_mem_support p.1.length
    exact (hsame.symm.trans hend) ▸ hqmem
  · right
    have hlen' : q.1.length ≤ p.1.length := by omega
    have hsame := G.rooted_paths_agree_until_shorter_ends
      p q hmax hroot q.1.length hlen' le_rfl
    have hend : q.1.getVert q.1.length = z := q.1.getVert_length
    have hpmem : p.1.getVert q.1.length ∈ p.1.support :=
      p.1.getVert_mem_support q.1.length
    exact (hsame.trans hend) ▸ hpmem

/-- In a degree-two graph, if an internal vertex of a simple path is
adjacent to the path's endpoint, it is the penultimate vertex. -/
theorem path_penultimate_of_internal_adj_endpoint
    {H : SimpleGraph G.V} {x y z : G.V}
    (q : H.Path x z) (hmax : ∀ v, H.degree v ≤ 2)
    (hy : y ∈ q.1.support) (hyx : y ≠ x) (hyz : y ≠ z)
    (hyzAdj : H.Adj y z) :
    q.1.getVert (q.1.length - 1) = y := by
  obtain ⟨j, hj, hjLe⟩ :=
    SimpleGraph.Walk.mem_support_iff_exists_getVert.mp hy
  have hjPos : 0 < j := by
    by_contra h
    have hj0 : j = 0 := by omega
    exact hyx (hj.symm.trans (by simpa [hj0] using q.1.getVert_zero))
  have hjLt : j < q.1.length := by
    by_contra h
    have hjEnd : j = q.1.length := by omega
    exact hyz (hj.symm.trans (by simpa [hjEnd] using q.1.getVert_length))
  have hprevAdj : H.Adj y (q.1.getVert (j-1)) := by
    have hidx : j - 1 + 1 = j := by omega
    simpa [←hj, hidx] using
      (q.1.adj_getVert_succ (i := j-1) (by omega)).symm
  have hnextAdj : H.Adj y (q.1.getVert (j+1)) := by
    simpa [←hj] using q.1.adj_getVert_succ (i := j) hjLt
  have hnextNePrev : q.1.getVert (j+1) ≠
      q.1.getVert (j-1) := by
    intro h
    have hinj := q.property.getVert_injOn
      (Set.mem_Iic.mpr (by omega : j+1 ≤ q.1.length))
      (Set.mem_Iic.mpr (by omega : j-1 ≤ q.1.length)) h
    omega
  have hendNePrev : z ≠ q.1.getVert (j-1) := by
    intro h
    have h' : q.1.getVert q.1.length = q.1.getVert (j-1) :=
      q.1.getVert_length.trans h
    have hinj := q.property.getVert_injOn
      (Set.mem_Iic.mpr le_rfl)
      (Set.mem_Iic.mpr (by omega : j-1 ≤ q.1.length)) h'
    omega
  have hnextEq : q.1.getVert (j+1) = z :=
    G.unique_nonbacktracking_neighbor_of_degree_le_two
      (hmax y) hprevAdj hnextAdj hyzAdj
      hnextNePrev hendNePrev
  have hidx : j + 1 = q.1.length := by
    have h' : q.1.getVert (j+1) = q.1.getVert q.1.length :=
      hnextEq.trans q.1.getVert_length.symm
    exact q.property.getVert_injOn
      (Set.mem_Iic.mpr (by omega : j+1 ≤ q.1.length))
      (Set.mem_Iic.mpr le_rfl) h'
  have hpen : q.1.length - 1 = j := by omega
  simpa [hpen] using hj

end WeightedEdgeColoring.WeightedMultigraph
