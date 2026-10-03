import WeightedEdgeColoring.SubtwoOrdinaryFivePresentFirstHitShape

/-!
# The internal `b` edge following any first return
-/

namespace WeightedEdgeColoring.WeightedMultigraph

universe u
variable (G : WeightedMultigraph.{u})

/-- The first return to an old five-path vertex follows its internal
`b` edge on the next step, provided the path does not end there. -/
theorem FivePathState.first_return_follows_internal_b_edge
    {F : Finset G.E} {k : ℕ} {a b c : Fin k}
    (s : G.FivePathState F k a b)
    (p : (G.twoColorGraph (F.erase s.omitted) s.paint b c).Path
      s.right s.left)
    {i : ℕ} (hi : 1 < i) (hiLt : i < p.1.length)
    (hfirst : ∀ j, 0 < j → j < i →
      p.1.getVert j ∉ s.path.1.support.toFinset)
    {g : G.E} (hgF : g ∈ F.erase s.omitted)
    (hgV : G.Inc (p.1.getVert i) g)
    {z : G.V} (hgz : G.Inc z g)
    (hvz : p.1.getVert i ≠ z)
    (hzS : z ∈ s.path.1.support.toFinset)
    (hgB : s.paint g = b) :
    p.1.getVert (i + 1) = z := by
  classical
  let H := G.twoColorGraph (F.erase s.omitted) s.paint b c
  have hVz : H.Adj (p.1.getVert i) z :=
    G.twoColorGraph_adj_of_witness_inc hvz hgF hgV hgz (Or.inl hgB)
  have hprevOut : p.1.getVert (i - 1) ∉
      s.path.1.support.toFinset :=
    hfirst (i - 1) (by omega) (by omega)
  have hprevNeZ : p.1.getVert (i - 1) ≠ z := by
    intro h
    apply hprevOut
    simpa only [h] using hzS
  have hidx : i - 1 + 1 = i := by omega
  have hprevAdj : H.Adj (p.1.getVert i) (p.1.getVert (i - 1)) := by
    simpa [hidx] using
      (p.1.adj_getVert_succ (i := i - 1) (by omega)).symm
  have hnextAdj : H.Adj (p.1.getVert i) (p.1.getVert (i + 1)) := by
    simpa using p.1.adj_getVert_succ (i := i) hiLt
  have hprevNeNext : p.1.getVert (i - 1) ≠ p.1.getVert (i + 1) := by
    intro h
    have hidxEq := p.property.getVert_injOn
      (Set.mem_Iic.mpr (by omega : i - 1 ≤ p.1.length))
      (Set.mem_Iic.mpr (by omega : i + 1 ≤ p.1.length)) h
    omega
  have hpairCard : ({p.1.getVert (i - 1), z} :
      Finset G.V).card = 2 := by simp [hprevNeZ]
  have hsubset : ({p.1.getVert (i - 1), z} : Finset G.V) ⊆
      H.neighborFinset (p.1.getVert i) := by
    intro v hv
    simp only [Finset.mem_insert, Finset.mem_singleton] at hv
    rcases hv with rfl | rfl
    · exact (H.mem_neighborFinset _ _).mpr hprevAdj
    · exact (H.mem_neighborFinset _ _).mpr hVz
  have hmax : H.degree (p.1.getVert i) ≤ 2 :=
    G.twoColorGraph_degree_le_two_of_isProperOn
      (F.erase s.omitted) s.paint s.proper b c _
  have hNcard : (H.neighborFinset (p.1.getVert i)).card ≤ 2 := by
    rw [H.card_neighborFinset_eq_degree]
    exact hmax
  have hEq : ({p.1.getVert (i - 1), z} : Finset G.V) =
      H.neighborFinset (p.1.getVert i) :=
    Finset.eq_of_subset_of_card_le hsubset (by omega)
  have hnextMem : p.1.getVert (i + 1) ∈
      ({p.1.getVert (i - 1), z} : Finset G.V) := by
    rw [hEq]
    exact (H.mem_neighborFinset _ _).mpr hnextAdj
  rcases Finset.mem_insert.mp hnextMem with hprev | hz
  · exact False.elim (hprevNeNext hprev.symm)
  · simpa using hz

/-- A first return at either middle vertex traverses the old middle
`b` edge next: `Z₂→Z₃` or `Z₃→Z₂`. -/
theorem FivePathState.first_return_middle_pair
    {F : Finset G.E} {k : ℕ} {a b c : Fin k}
    (s : G.FivePathState F k a b)
    (p : (G.twoColorGraph (F.erase s.omitted) s.paint b c).Path
      s.right s.left)
    {i : ℕ} (hi : 1 < i) (hiLe : i ≤ p.1.length)
    (hfirst : ∀ j, 0 < j → j < i →
      p.1.getVert j ∉ s.path.1.support.toFinset)
    (hcase : p.1.getVert i = s.path.1.getVert 2 ∨
      p.1.getVert i = s.path.1.getVert 3) :
    (p.1.getVert i = s.path.1.getVert 2 ∧
      p.1.getVert (i + 1) = s.path.1.getVert 3) ∨
    (p.1.getVert i = s.path.1.getVert 3 ∧
      p.1.getVert (i + 1) = s.path.1.getVert 2) := by
  obtain ⟨g₁, g₂, g₃, _, _, _, _,
    hg₂F, hg₂2, hg₂3, hg₂B, _, _, _, _⟩ :=
    FivePathState.exists_three_surviving_path_edges G s
  have hZ2mem : s.path.1.getVert 2 ∈ s.path.1.support.toFinset := by
    simpa only [List.mem_toFinset] using s.path.1.getVert_mem_support 2
  have hZ3mem : s.path.1.getVert 3 ∈ s.path.1.support.toFinset := by
    simpa only [List.mem_toFinset] using s.path.1.getVert_mem_support 3
  have hZ23ne : s.path.1.getVert 2 ≠ s.path.1.getVert 3 :=
    (s.path.1.adj_getVert_succ
      (i := 2) (by have := s.path_len; omega)).ne
  rcases hcase with hZ2 | hZ3
  · have hZ2neL :=
      (FivePathState.internal_vertex_ne_endpoints G s
        (by omega : 0 < 2) (by omega : 2 < 4)).1
    have hiLt : i < p.1.length := by
      have hne : i ≠ p.1.length := by
        intro h
        exact hZ2neL (hZ2.symm.trans
          (by simpa [h] using p.1.getVert_length))
      omega
    have hnext := FivePathState.first_return_follows_internal_b_edge
      G s p hi hiLt hfirst hg₂F (hZ2 ▸ hg₂2) hg₂3
      (hZ2 ▸ hZ23ne) hZ3mem hg₂B
    exact Or.inl ⟨hZ2, hnext⟩
  · have hZ3neL :=
      (FivePathState.internal_vertex_ne_endpoints G s
        (by omega : 0 < 3) (by omega : 3 < 4)).1
    have hiLt : i < p.1.length := by
      have hne : i ≠ p.1.length := by
        intro h
        exact hZ3neL (hZ3.symm.trans
          (by simpa [h] using p.1.getVert_length))
      omega
    have hnext := FivePathState.first_return_follows_internal_b_edge
      G s p hi hiLt hfirst hg₂F (hZ3 ▸ hg₂3) hg₂2
      (hZ3 ▸ hZ23ne.symm) hZ2mem hg₂B
    exact Or.inr ⟨hZ3, hnext⟩

end WeightedEdgeColoring.WeightedMultigraph
