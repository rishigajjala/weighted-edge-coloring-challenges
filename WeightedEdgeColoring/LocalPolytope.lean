import WeightedEdgeColoring.WeightedGraph

open scoped BigOperators

namespace WeightedEdgeColoring
namespace WeightedSimpleGraph

variable (G : WeightedSimpleGraph)

/-- A subset of one vertex star that fits into one unit-capacity color. -/
def StarFeasible (v : G.V) (S : Finset (G.StarEdge v)) : Prop :=
  ∑ e ∈ S, G.weight e.1 ≤ 1

/-- A vector on one star belongs to the local packing polytope when it is
the marginal vector of a finite probability distribution on feasible star
subsets. The finite sample space is represented explicitly by a finite type. -/
def IsAverageOfStarFeasibleSets (v : G.V)
    (x : G.StarEdge v → ℝ) : Prop :=
  ∃ (m : ℕ) (p : Fin m → ℝ)
      (outcome : Fin m → Finset (G.StarEdge v)),
    (∀ i, 0 ≤ p i) ∧
    (∑ i, p i = 1) ∧
    (∀ i, G.StarFeasible v (outcome i)) ∧
    (∀ e, (∑ i, if e ∈ outcome i then p i else 0) = x e)

/-- The fiber of one local bin is a feasible star subset. -/
theorem starFeasible_binFiber
    {v : G.V} {n : ℕ} (bin : G.StarEdge v → Fin n)
    (hbin : ∀ i, G.starBinLoad bin i ≤ 1) (i : Fin n) :
    G.StarFeasible v (Finset.univ.filter fun e => bin e = i) := by
  simpa only [StarFeasible, starBinLoad, Finset.sum_filter] using hbin i

/-- A packing of a star into a positive number of bins represents the
constant reciprocal vector as the uniform average of those feasible bins. -/
theorem uniform_average_of_packsStarInto
    {v : G.V} {n : ℕ} (hn : 0 < n) (hpack : G.PacksStarInto v n) :
    G.IsAverageOfStarFeasibleSets v
      (fun _ => 1 / (n : ℝ)) := by
  rcases hpack with ⟨bin, hbin⟩
  let outcome : Fin n → Finset (G.StarEdge v) :=
    fun i => Finset.univ.filter fun e => bin e = i
  refine ⟨n, (fun _ => 1 / (n : ℝ)), outcome, ?_, ?_, ?_, ?_⟩
  · intro i
    exact one_div_nonneg.mpr (Nat.cast_nonneg n)
  · have hn0 : (n : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hn)
    simp [hn0]
  · intro i
    exact G.starFeasible_binFiber bin hbin i
  · intro e
    simp [outcome]

/-- The uniform proposals used in the coefficient-one proof lie in every
local packing polytope. -/
theorem uniform_local_proposals_of_locallyPacksInto
    {n : ℕ} (hn : 0 < n) (hpack : G.LocallyPacksInto n) :
    ∀ v, G.IsAverageOfStarFeasibleSets v
      (fun _ => 1 / (n : ℝ)) := by
  intro v
  exact G.uniform_average_of_packsStarInto hn (hpack v)

end WeightedSimpleGraph
end WeightedEdgeColoring
