import WeightedEdgeColoring.BPGeneralOddSetDensity

/-!
# Finite search for ordinary coloring certificates

For a fixed finite indexed multigraph, edge set, and palette size, ordinary
proper colorability is computably decidable by exhaustive search.  This is
useful for checking concrete certificates, but it does not prove a uniform
Goldberg--Seymour bound: such a theorem must still construct or bound a
successful palette for graphs of arbitrary finite size.
-/

namespace WeightedEdgeColoring
namespace WeightedMultigraph

universe u

variable (G : WeightedMultigraph.{u})

def HasProperColoringOn (F : Finset G.E) (q : ℕ) : Prop :=
  ∃ color : G.E → Fin q, G.IsProperOn F color

instance instDecidableHasProperColoringOn (F : Finset G.E) (q : ℕ) :
    Decidable (G.HasProperColoringOn F q) := by
  unfold HasProperColoringOn IsProperOn Set.InjOn
  infer_instance

/-- Executable exhaustive search result for one fixed finite instance. -/
def ordinaryColoringSearch (F : Finset G.E) (q : ℕ) : Bool :=
  decide (G.HasProperColoringOn F q)

theorem ordinaryColoringSearch_eq_true_iff (F : Finset G.E) (q : ℕ) :
    G.ordinaryColoringSearch F q = true ↔ G.HasProperColoringOn F q := by
  simp [ordinaryColoringSearch]

end WeightedMultigraph
end WeightedEdgeColoring
