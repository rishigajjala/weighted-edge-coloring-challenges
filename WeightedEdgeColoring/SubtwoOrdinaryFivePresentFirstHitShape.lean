import WeightedEdgeColoring.SubtwoOrdinaryFivePresentBoundaryPair

/-!
# Shape of the component path after its first return at `Z₁`
-/

namespace WeightedEdgeColoring.WeightedMultigraph

universe u
variable (G : WeightedMultigraph.{u})

/-- If the ordered right `(b,c)` path first returns to the old
five-path at `Z₁`, its next vertex is `X`. Thus `Z₁` is the penultimate
vertex of that path. -/
theorem FivePathState.first_return_at_z1_then_left
    {F : Finset G.E} {k : ℕ} {a b c : Fin k}
    (s : G.FivePathState F k a b)
    (p : (G.twoColorGraph (F.erase s.omitted) s.paint b c).Path
      s.right s.left)
    {i : ℕ} (hi : 1 < i) (hiLe : i ≤ p.1.length)
    (hfirst : ∀ j, 0 < j → j < i →
      p.1.getVert j ∉ s.path.1.support.toFinset)
    (hiZ1 : p.1.getVert i = s.path.1.getVert 1) :
    p.1.getVert (i + 1) = s.left ∧ i + 1 = p.1.length := by
  classical
  let H := G.twoColorGraph (F.erase s.omitted) s.paint b c
  have hZ1neL :=
    (FivePathState.internal_vertex_ne_endpoints G s
      (by omega : 0 < 1) (by omega : 1 < 4)).1
  have hiLt : i < p.1.length := by
    have hne : i ≠ p.1.length := by
      intro h
      exact hZ1neL (hiZ1.symm.trans
        (by simpa [h] using p.1.getVert_length))
    omega
  obtain ⟨g, hgF, hgL, hg1, hgB⟩ :=
    FivePathState.exists_first_b_edge G s
  have hZ1L : H.Adj (p.1.getVert i) s.left := by
    exact G.twoColorGraph_adj_of_witness_inc
      (hiZ1 ▸ hZ1neL) hgF (hiZ1 ▸ hg1) hgL (Or.inl hgB)
  have hprevOut : p.1.getVert (i - 1) ∉
      s.path.1.support.toFinset :=
    hfirst (i - 1) (by omega) (by omega)
  have hLmem : s.left ∈ s.path.1.support.toFinset := by
    simpa only [List.mem_toFinset] using s.path.1.start_mem_support
  have hprevNeL : p.1.getVert (i - 1) ≠ s.left := by
    intro h
    apply hprevOut
    simpa only [h] using hLmem
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
  have hpairCard : ({p.1.getVert (i - 1), s.left} :
      Finset G.V).card = 2 := by simp [hprevNeL]
  have hsubset : ({p.1.getVert (i - 1), s.left} : Finset G.V) ⊆
      H.neighborFinset (p.1.getVert i) := by
    intro v hv
    simp only [Finset.mem_insert, Finset.mem_singleton] at hv
    rcases hv with rfl | rfl
    · exact (H.mem_neighborFinset _ _).mpr hprevAdj
    · exact (H.mem_neighborFinset _ _).mpr hZ1L
  have hmax : H.degree (p.1.getVert i) ≤ 2 :=
    G.twoColorGraph_degree_le_two_of_isProperOn
      (F.erase s.omitted) s.paint s.proper b c _
  have hNcard : (H.neighborFinset (p.1.getVert i)).card ≤ 2 := by
    rw [H.card_neighborFinset_eq_degree]
    exact hmax
  have hEq : ({p.1.getVert (i - 1), s.left} : Finset G.V) =
      H.neighborFinset (p.1.getVert i) :=
    Finset.eq_of_subset_of_card_le hsubset (by omega)
  have hnextMem : p.1.getVert (i + 1) ∈
      ({p.1.getVert (i - 1), s.left} : Finset G.V) := by
    rw [hEq]
    exact (H.mem_neighborFinset _ _).mpr hnextAdj
  have hnextL : p.1.getVert (i + 1) = s.left := by
    rcases Finset.mem_insert.mp hnextMem with hprev | hleft
    · exact False.elim (hprevNeNext hprev.symm)
    · simpa using hleft
  have hidxEnd : i + 1 = p.1.length := by
    apply p.property.getVert_injOn
      (Set.mem_Iic.mpr (by omega : i + 1 ≤ p.1.length))
      (Set.mem_Iic.mpr (le_refl _))
    simpa only [p.1.getVert_length] using hnextL
  exact ⟨hnextL, hidxEnd⟩

end WeightedEdgeColoring.WeightedMultigraph
