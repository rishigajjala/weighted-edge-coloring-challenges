import WeightedEdgeColoring.SubtwoOrdinaryFivePresentMiddleOrder

/-!
# Exact order of the middle adjacent pair on the Y-rooted chain
-/

namespace WeightedEdgeColoring.WeightedMultigraph

universe u
variable (G : WeightedMultigraph.{u})

/-- The later of `Z₂,Z₃` on Y's `(b,c)` chain is immediately
preceded by the other: the old `b` edge is the last edge of one of
the two ordered paths. -/
theorem FivePathState.exists_middle_pair_penultimate_order
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
        (q₃.1.getVert (q₃.1.length - 1) =
            s.path.1.getVert 2 ∨
          q₂.1.getVert (q₂.1.length - 1) =
            s.path.1.getVert 3) := by
  classical
  obtain ⟨q₂,q₃,hq₂Len,hq₃Len,hX₂,hX₃,horder⟩ :=
    FivePathState.exists_ordered_middle_paths_after_left
      G s hcritical hdk hdegree hthreshold
      hnot hleft hright hZ1 p hi hiLe hfirst hiZ1 hnoMiddle
  let H := G.twoColorGraph (F.erase s.omitted) s.paint b c
  have hmax : ∀ v, H.degree v ≤ 2 := by
    intro v
    exact G.twoColorGraph_degree_le_two_of_isProperOn
      (F.erase s.omitted) s.paint s.proper b c v
  obtain ⟨_, g₂, _, _, _, _, _,
    hg₂F, hg₂2, hg₂3, hg₂B, _, _, _, _⟩ :=
    FivePathState.exists_three_surviving_path_edges G s
  have hZ23 : H.Adj (s.path.1.getVert 2)
      (s.path.1.getVert 3) :=
    G.twoColorGraph_adj_of_witness_inc
      (s.path.1.adj_getVert_succ
        (i := 2) (by have := s.path_len; omega)).ne
      hg₂F hg₂2 hg₂3 (Or.inl hg₂B)
  have hZ2Y : s.path.1.getVert 2 ≠ s.right :=
    (FivePathState.internal_vertex_ne_endpoints G s
      (by omega : 0 < 2) (by omega : 2 < 4)).2
  have hZ3Y : s.path.1.getVert 3 ≠ s.right :=
    (FivePathState.internal_vertex_ne_endpoints G s
      (by omega : 0 < 3) (by omega : 3 < 4)).2
  have hZ23ne : s.path.1.getVert 2 ≠ s.path.1.getVert 3 := hZ23.ne
  have hpen : q₃.1.getVert (q₃.1.length - 1) =
        s.path.1.getVert 2 ∨
      q₂.1.getVert (q₂.1.length - 1) =
        s.path.1.getVert 3 := by
    rcases horder with hZ2onQ3 | hZ3onQ2
    · exact Or.inl (G.path_penultimate_of_internal_adj_endpoint
        q₃ hmax hZ2onQ3 hZ2Y hZ23ne hZ23)
    · exact Or.inr (G.path_penultimate_of_internal_adj_endpoint
        q₂ hmax hZ3onQ2 hZ3Y hZ23ne.symm hZ23.symm)
  exact ⟨q₂,q₃,hq₂Len,hq₃Len,hX₂,hX₃,hpen⟩

end WeightedEdgeColoring.WeightedMultigraph
