import WeightedEdgeColoring.FinitePaletteMerge

/-!
# Bin-packing facts for edge restrictions

The two `bp(G)` proofs repeatedly color a selected edge set and its
complement with separate palettes.  This file records that restricting the
edge type preserves bipartiteness and cannot increase the common local
bin-packing number.
-/

open scoped BigOperators

namespace WeightedEdgeColoring
namespace WeightedMultigraph

universe u

variable (G : WeightedMultigraph.{u})

/-- Restrict a bipartition certificate to a set of indexed edges. -/
def Bipartition.edgeRestriction (b : G.Bipartition) (R : Finset G.E) :
    (G.edgeRestriction R).Bipartition where
  side := b.side
  opposite e := b.opposite e.1

theorem edgeRestriction_isBipartite (R : Finset G.E)
    (h : G.IsBipartite) :
    (G.edgeRestriction R).IsBipartite := by
  rcases h with ⟨b⟩
  exact ⟨Bipartition.edgeRestriction G b R⟩

/-- A local packing restricts to every edge subset. -/
theorem edgeRestriction_locallyPacksInto (R : Finset G.E) {n : ℕ}
    (h : G.LocallyPacksInto n) :
    (G.edgeRestriction R).LocallyPacksInto n := by
  classical
  intro v
  rcases h v with ⟨bin, hbin⟩
  let embed : (G.edgeRestriction R).StarEdge v ↪ G.StarEdge v :=
    ⟨fun e ↦ ⟨e.1.1, by simpa using e.2⟩, by
      intro e f hef
      apply Subtype.ext
      apply Subtype.ext
      exact congrArg (fun z : G.StarEdge v ↦ z.1) hef⟩
  let restrictedBin : (G.edgeRestriction R).StarEdge v → Fin n :=
    fun e ↦ bin (embed e)
  refine ⟨restrictedBin, ?_⟩
  intro i
  let term : G.StarEdge v → ℝ := fun e ↦
    if bin e = i then G.weight e.1 else 0
  have hnonneg : ∀ e : G.StarEdge v, 0 ≤ term e := by
    intro e
    dsimp [term]
    split
    · exact G.weight_nonneg e.1
    · exact le_rfl
  calc
    (G.edgeRestriction R).starBinLoad restrictedBin i =
        ∑ e ∈ (Finset.univ.map embed), term e := by
      rw [Finset.sum_map]
      rfl
    _ ≤ ∑ e ∈ (Finset.univ : Finset (G.StarEdge v)), term e := by
      exact Finset.sum_le_sum_of_subset_of_nonneg
        (Finset.subset_univ _) (fun e _he _hnot ↦ hnonneg e)
    _ = G.starBinLoad bin i := by
      simp only [term, starBinLoad]
    _ ≤ 1 := hbin i

theorem edgeRestriction_bp_le (R : Finset G.E) :
    (G.edgeRestriction R).bp ≤ G.bp := by
  apply (G.edgeRestriction R).bp_le_of_locallyPacksInto
  exact G.edgeRestriction_locallyPacksInto R G.locallyPacksInto_bp

end WeightedMultigraph
end WeightedEdgeColoring
