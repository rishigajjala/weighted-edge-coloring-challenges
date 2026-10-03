import WeightedEdgeColoring.MultigraphTinyEdgeRounding
import WeightedEdgeColoring.MultigraphPackingBounds
import WeightedEdgeColoring.FiniteCategoricalSelection
import WeightedEdgeColoring.LargeStarCategoricalDependency

/-!
# Large-star bounds and local categorical dependencies

After edges below a fixed threshold are reserved for deterministic rounding,
only the remaining large edges enter profile synchronization.  This file
records the elementary bound on their number and the generic support-overlap
count used by an ordinary categorical local lemma.
-/

open scoped BigOperators

namespace WeightedEdgeColoring

noncomputable section

namespace WeightedMultigraph

universe u

variable (G : WeightedMultigraph.{u})

/-- Edges at a vertex whose weight is at least `beta`. -/
def largeStarEdges (beta : ℝ) (v : G.V) : Finset (G.StarEdge v) :=
  Finset.univ.filter fun e ↦ beta ≤ G.weight e.1

@[simp] theorem mem_largeStarEdges {beta : ℝ} {v : G.V} {e : G.StarEdge v} :
    e ∈ G.largeStarEdges beta v ↔ beta ≤ G.weight e.1 := by
  simp [largeStarEdges]

/-- The number of `beta`-large edges times `beta` is at most the star load. -/
theorem largeStarEdges_card_mul_beta_le_starWeight
    (beta : ℝ) (v : G.V) :
    ((G.largeStarEdges beta v).card : ℝ) * beta ≤ G.starWeight v := by
  calc
    ((G.largeStarEdges beta v).card : ℝ) * beta =
        ∑ _e ∈ G.largeStarEdges beta v, beta := by simp
    _ ≤ ∑ e ∈ G.largeStarEdges beta v, G.weight e.1 := by
      apply Finset.sum_le_sum
      intro e he
      exact (G.mem_largeStarEdges).mp he
    _ ≤ ∑ e : G.StarEdge v, G.weight e.1 := by
      exact Finset.sum_le_sum_of_subset_of_nonneg
        (fun _ _ ↦ Finset.mem_univ _)
        (fun e _ _ ↦ G.weight_nonneg e.1)
    _ = G.starWeight v := rfl

/-- Under an `n`-bin local packing, a star has weighted large-edge count at
most `n / beta`. -/
theorem largeStarEdges_card_le_div_of_locallyPacksInto
    {n : ℕ} (hlocal : G.LocallyPacksInto n)
    {beta : ℝ} (hbeta : 0 < beta) (v : G.V) :
    ((G.largeStarEdges beta v).card : ℝ) ≤ (n : ℝ) / beta := by
  apply (le_div_iff₀ hbeta).2
  exact (G.largeStarEdges_card_mul_beta_le_starWeight beta v).trans
    (G.starWeight_le_of_locallyPacksInto hlocal v)

/-- Natural-number form: any `K` with `n < (K+1) beta` bounds the number of
large edges at every star by `K`. -/
theorem largeStarEdges_card_le_of_locallyPacksInto
    {n K : ℕ} (hlocal : G.LocallyPacksInto n)
    {beta : ℝ} (hbeta : 0 < beta)
    (hK : (n : ℝ) < ((K + 1 : ℕ) : ℝ) * beta)
    (v : G.V) :
    (G.largeStarEdges beta v).card ≤ K := by
  by_contra hnot
  have hKcard : K + 1 ≤ (G.largeStarEdges beta v).card := by omega
  have hcast : ((K + 1 : ℕ) : ℝ) ≤
      ((G.largeStarEdges beta v).card : ℝ) := by
    exact_mod_cast hKcard
  have hmul : ((K + 1 : ℕ) : ℝ) * beta ≤
      ((G.largeStarEdges beta v).card : ℝ) * beta :=
    mul_le_mul_of_nonneg_right hcast hbeta.le
  have hstar := G.largeStarEdges_card_mul_beta_le_starWeight beta v
  have hn := G.starWeight_le_of_locallyPacksInto hlocal v
  linarith

end WeightedMultigraph


/-! Generic categorical support-overlap declarations are shared with
`LargeStarCategoricalDependency`. -/

end

end WeightedEdgeColoring
