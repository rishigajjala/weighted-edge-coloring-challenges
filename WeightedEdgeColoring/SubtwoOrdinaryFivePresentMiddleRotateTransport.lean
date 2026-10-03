import WeightedEdgeColoring.SubtwoOrdinaryFivePresentMiddleOppositeSuffixActual

/-!
# Exterior path transport through the four-edge rotation
-/

namespace WeightedEdgeColoring.WeightedMultigraph

universe u
variable (G : WeightedMultigraph.{u})

/-- An exterior two-color path survives a rotation of the omitted edge
around the same five-vertex support when the paint is fixed at every
outside endpoint. -/
theorem FivePathState.transfer_exterior_path_of_outside_stability
    {F : Finset G.E} {k : ℕ} {a b a' b' c : Fin k}
    (s : G.FivePathState F k a b)
    (t : G.FivePathState F k a' b')
    (hsupport : t.path.1.support.toFinset =
      s.path.1.support.toFinset)
    (hstable : ∀ v, v ∉ s.path.1.support.toFinset →
      ∀ r, G.Inc v r → t.paint r = s.paint r)
    {x y : G.V}
    (q : (G.twoColorGraph (F.erase s.omitted) s.paint b c).Path x y)
    (hexterior : ∀ e ∈ q.1.edges, ∀ u v, e = s(u,v) →
      ¬(u ∈ s.path.1.support ∧ v ∈ s.path.1.support)) :
    ∃ q' : (G.twoColorGraph (F.erase t.omitted) t.paint b c).Path x y,
      q'.1.support = q.1.support ∧
      q'.1.length = q.1.length ∧
      q'.1.edges = q.1.edges := by
  let H' := G.twoColorGraph (F.erase t.omitted) t.paint b c
  have hedges : ∀ e ∈ q.1.edges, e ∈ H'.edgeSet := by
    intro e he
    induction e using Sym2.inductionOn with
    | _ u v =>
      have huv : (G.twoColorGraph (F.erase s.omitted) s.paint b c).Adj u v :=
        q.1.edges_subset_edgeSet he
      obtain ⟨r,hrOld,hrU,hrV,hrColor⟩ :=
        G.exists_twoColorWitnessEdge (F.erase s.omitted) s.paint b c huv
      have hnotBoth : ¬(u ∈ s.path.1.support ∧
          v ∈ s.path.1.support) := hexterior s(u,v) he u v rfl
      have hOut : u ∉ s.path.1.support.toFinset ∨
          v ∉ s.path.1.support.toFinset := by
        simpa only [List.mem_toFinset] using not_and_or.mp hnotBoth
      have hrNe : r ≠ t.omitted := by
        intro heq
        subst r
        have hEnds := G.endpoint_eq_or_endpoint_eq_swap_of_inc
          t.left_ne_right t.left_inc t.right_inc
        have hUin : u ∈ t.path.1.support.toFinset := by
          rcases hEnds with ⟨hf,hs⟩ | ⟨hf,hs⟩
          · rcases hrU with hu | hu
            · rw [← hu, hf]
              simpa only [List.mem_toFinset] using t.path.1.start_mem_support
            · rw [← hu, hs]
              simpa only [List.mem_toFinset] using t.path.1.end_mem_support
          · rcases hrU with hu | hu
            · rw [← hu, hf]
              simpa only [List.mem_toFinset] using t.path.1.end_mem_support
            · rw [← hu, hs]
              simpa only [List.mem_toFinset] using t.path.1.start_mem_support
        have hVin : v ∈ t.path.1.support.toFinset := by
          rcases hEnds with ⟨hf,hs⟩ | ⟨hf,hs⟩
          · rcases hrV with hv | hv
            · rw [← hv, hf]
              simpa only [List.mem_toFinset] using t.path.1.start_mem_support
            · rw [← hv, hs]
              simpa only [List.mem_toFinset] using t.path.1.end_mem_support
          · rcases hrV with hv | hv
            · rw [← hv, hf]
              simpa only [List.mem_toFinset] using t.path.1.end_mem_support
            · rw [← hv, hs]
              simpa only [List.mem_toFinset] using t.path.1.start_mem_support
        rcases hOut with huOut | hvOut
        · exact huOut (by simpa [hsupport] using hUin)
        · exact hvOut (by simpa [hsupport] using hVin)
      have hrNew : r ∈ F.erase t.omitted :=
        Finset.mem_erase.mpr ⟨hrNe,(Finset.mem_erase.mp hrOld).2⟩
      have hrColorNew : t.paint r = b ∨ t.paint r = c := by
        rcases hOut with huOut | hvOut
        · rw [hstable u huOut r hrU]
          exact hrColor
        · rw [hstable v hvOut r hrV]
          exact hrColor
      exact G.twoColorGraph_adj_of_witness_inc huv.ne
        hrNew hrU hrV hrColorNew
  let q' : H'.Path x y :=
    ⟨q.1.transfer H' hedges,q.property.transfer hedges⟩
  exact ⟨q',q.1.support_transfer hedges,
    q.1.length_transfer hedges,q.1.edges_transfer hedges⟩

end WeightedEdgeColoring.WeightedMultigraph
