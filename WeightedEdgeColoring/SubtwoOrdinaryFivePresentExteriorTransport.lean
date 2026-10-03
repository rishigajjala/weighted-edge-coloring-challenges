import WeightedEdgeColoring.SubtwoOrdinaryFivePresentABThenShift

/-!
# Exterior two-color path transport through the critical-chain switch
-/

namespace WeightedEdgeColoring.WeightedMultigraph

universe u
variable (G : WeightedMultigraph.{u})

/-- If a path meets a distinguished vertex set only at its endpoints
and those endpoints are nonadjacent, each path edge has a vertex
outside the set. -/
theorem exterior_edges_of_endpoint_only_support
    (H : SimpleGraph G.V) (S : Set G.V) {x y : G.V}
    (q : H.Path x y)
    (hcap : ∀ v ∈ q.1.support, v ∈ S → v = x ∨ v = y)
    (hno : ¬H.Adj x y) :
    ∀ e ∈ q.1.edges, ∀ u v, e = s(u,v) →
      ¬(u ∈ S ∧ v ∈ S) := by
  intro e he u v huv ⟨huS,hvS⟩
  subst e
  have hadj : H.Adj u v := q.1.edges_subset_edgeSet he
  have hu : u = x ∨ u = y :=
    hcap u (q.1.fst_mem_support_of_mem_edges he) huS
  have hv : v = x ∨ v = y :=
    hcap v (q.1.snd_mem_support_of_mem_edges he) hvS
  rcases hu with rfl | rfl <;> rcases hv with rfl | rfl
  · exact hadj.ne rfl
  · exact hno hadj
  · exact hno hadj.symm
  · exact hadj.ne rfl

/-- Every edge of an exterior `(b,c)` path survives the `(a,b)`
critical-chain switch. This formulation applies both to the prefix
before `Z₁` and to the suffix after `X` in the no-middle-`c` case. -/
theorem FivePathState.transfer_exterior_bc_path_after_ab_switch
    {F : Finset G.E} {k : ℕ} {a b c : Fin k}
    (s : G.FivePathState F k a b)
    (hca : c ≠ a) (hcb : c ≠ b)
    {switched : G.E → Fin k}
    (hother : ∀ r, s.paint r ≠ a → s.paint r ≠ b →
      switched r = s.paint r)
    (hstable : ∀ v, v ∉ s.path.1.support →
      ∀ r ∈ F.erase s.omitted, G.Inc v r →
        switched r = s.paint r)
    {x y : G.V}
    (q : (G.twoColorGraph (F.erase s.omitted) s.paint b c).Path x y)
    (hexterior : ∀ e ∈ q.1.edges,
      ∀ u v, e = s(u,v) →
        ¬(u ∈ s.path.1.support ∧ v ∈ s.path.1.support)) :
    ∃ q' : (G.twoColorGraph (F.erase s.omitted) switched b c).Path x y,
      q'.1.support = q.1.support ∧ q'.1.length = q.1.length ∧
        q'.1.edges = q.1.edges := by
  let H' := G.twoColorGraph (F.erase s.omitted) switched b c
  have hedges : ∀ e ∈ q.1.edges, e ∈ H'.edgeSet := by
    intro e he
    induction e using Sym2.inductionOn with
    | _ u v =>
      have huv : (G.twoColorGraph (F.erase s.omitted) s.paint b c).Adj u v :=
        q.1.edges_subset_edgeSet he
      obtain ⟨r, hrF, hrU, hrV, hrColor⟩ :=
        G.exists_twoColorWitnessEdge (F.erase s.omitted) s.paint b c huv
      have hnotBoth : ¬(u ∈ s.path.1.support ∧ v ∈ s.path.1.support) :=
        hexterior s(u,v) he u v rfl
      have hrNew : switched r = b ∨ switched r = c := by
        rcases hrColor with hrB | hrC
        · by_cases huS : u ∈ s.path.1.support
          · have hvOut : v ∉ s.path.1.support := by
              intro hvS; exact hnotBoth ⟨huS,hvS⟩
            exact Or.inl ((hstable v hvOut r hrF hrV).trans hrB)
          · exact Or.inl ((hstable u huS r hrF hrU).trans hrB)
        · have hra : s.paint r ≠ a := by simpa [hrC] using hca
          have hrb : s.paint r ≠ b := by simpa [hrC] using hcb
          exact Or.inr ((hother r hra hrb).trans hrC)
      exact G.twoColorGraph_adj_of_witness_inc huv.ne hrF hrU hrV hrNew
  let qWalk := q.1.transfer H' hedges
  let q' : H'.Path x y := ⟨qWalk, q.property.transfer hedges⟩
  refine ⟨q', ?_, ?_, ?_⟩
  · exact q.1.support_transfer hedges
  · exact q.1.length_transfer hedges
  · exact q.1.edges_transfer hedges

end WeightedEdgeColoring.WeightedMultigraph
