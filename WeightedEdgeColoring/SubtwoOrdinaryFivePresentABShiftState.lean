import WeightedEdgeColoring.SubtwoOrdinaryFivePresentMiddlePenultimate

/-!
# A normalized five-path state after the first critical-chain switch
-/

namespace WeightedEdgeColoring.WeightedMultigraph

universe u
variable (G : WeightedMultigraph.{u})

private theorem getVert_transfer
    {H K : SimpleGraph G.V} {x y : G.V}
    (p : H.Walk x y) (hedges : ∀ e ∈ p.edges, e ∈ K.edgeSet)
    (j : ℕ) : (p.transfer K hedges).getVert j = p.getVert j := by
  induction p generalizing j with
  | nil =>
      simp [SimpleGraph.Walk.transfer]
  | @cons x z y hxz p ih =>
      cases j with
      | zero => simp
      | succ j =>
          have htail : ∀ e ∈ p.edges, e ∈ K.edgeSet := by
            intro e he
            exact hedges e (by simpa only [SimpleGraph.Walk.edges_cons,
              List.mem_cons] using (Or.inr he))
          have h := ih htail j
          simpa [SimpleGraph.Walk.transfer,
            SimpleGraph.Walk.getVert_cons_succ] using h

/-- Switching the old critical `(a,b)` component gives a new
five-path state with endpoint colors `(b,a)` on the same omitted edge
and the same ordered vertex path. -/
theorem FivePathState.exists_ab_switched_state
    {F : Finset G.E} {k : ℕ} {a b : Fin k}
    (s : G.FivePathState F k a b)
    (hcritical : G.IsColorCriticalOn F k) :
    ∃ t : G.FivePathState F k b a,
      t.omitted = s.omitted ∧
      t.left = s.left ∧ t.right = s.right ∧
      t.path.1.support = s.path.1.support ∧
      (∀ j, t.path.1.getVert j = s.path.1.getVert j) ∧
      (∀ r, s.paint r ≠ a → s.paint r ≠ b →
        t.paint r = s.paint r) ∧
      (∀ c, c ≠ a → c ≠ b → ∀ v,
        FivePathState.HasExternalColorAt G s c v →
          FivePathState.HasExternalColorAt G t c v) ∧
      (∀ v, v ∉ s.path.1.support →
        ∀ r ∈ F.erase s.omitted, G.Inc v r →
          t.paint r = s.paint r) := by
  obtain ⟨switched,hproper,hswapA,hswapB,hother,hstable⟩ :=
    FivePathState.exists_ab_path_switch_stable_outside
      G s hcritical
  have hmissing := FivePathState.ab_path_switch_missing_endpoints
    G s hswapA hswapB hother
  let H' := G.twoColorGraph (F.erase s.omitted) switched b a
  have hedges : ∀ e ∈ s.path.1.edges, e ∈ H'.edgeSet := by
    intro e he
    induction e using Sym2.inductionOn with
    | _ u v =>
      have huv : (G.twoColorGraph (F.erase s.omitted) s.paint a b).Adj u v :=
        s.path.1.edges_subset_edgeSet he
      obtain ⟨r,hrF,hrU,hrV,hrColor⟩ :=
        G.exists_twoColorWitnessEdge
          (F.erase s.omitted) s.paint a b huv
      have huS : u ∈ s.path.1.support :=
        s.path.1.fst_mem_support_of_mem_edges he
      have hrNew : switched r = b ∨ switched r = a := by
        rcases hrColor with hrA | hrB
        · exact Or.inl (hswapA u huS r hrF hrU hrA)
        · exact Or.inr (hswapB u huS r hrF hrU hrB)
      exact G.twoColorGraph_adj_of_witness_inc huv.ne
        hrF hrU hrV hrNew
  let q : H'.Path s.left s.right :=
    ⟨s.path.1.transfer H' hedges,
      s.path.property.transfer hedges⟩
  have hqSupport : q.1.support = s.path.1.support := by
    change (s.path.1.transfer H' hedges).support = s.path.1.support
    exact s.path.1.support_transfer hedges
  have hqLen : q.1.length = 4 := by
    change (s.path.1.transfer H' hedges).length = 4
    rw [s.path.1.length_transfer hedges]
    exact s.path_len
  have hqVerts : ∀ j, q.1.getVert j = s.path.1.getVert j := by
    intro j
    change (s.path.1.transfer H' hedges).getVert j =
      s.path.1.getVert j
    exact G.getVert_transfer s.path.1 hedges j
  let t : G.FivePathState F k b a := {
    omitted := s.omitted
    paint := switched
    left := s.left
    right := s.right
    omitted_mem := s.omitted_mem
    left_ne_right := s.left_ne_right
    left_inc := s.left_inc
    right_inc := s.right_inc
    proper := hproper
    left_missing := hmissing.1
    right_missing := hmissing.2
    path := q
    path_len := hqLen
  }
  have hexternal : ∀ c, c ≠ a → c ≠ b → ∀ v,
      FivePathState.HasExternalColorAt G s c v →
        FivePathState.HasExternalColorAt G t c v := by
    intro c hca hcb v hExt
    obtain ⟨r,hrF,hrV,hrC,hrOut⟩ := hExt
    refine ⟨r,hrF,hrV,?_,?_⟩
    · exact (hother r (by simpa [hrC] using hca)
        (by simpa [hrC] using hcb)).trans hrC
    · change r ∉ G.internalEdges (F.erase s.omitted)
        q.1.support.toFinset
      simpa only [hqSupport] using hrOut
  exact ⟨t,rfl,rfl,rfl,hqSupport,hqVerts,hother,
    hexternal,hstable⟩

end WeightedEdgeColoring.WeightedMultigraph
