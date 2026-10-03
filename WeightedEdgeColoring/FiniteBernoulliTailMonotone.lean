import WeightedEdgeColoring.FiniteBernoulliHarris

/-!
# Monotonicity of finite Bernoulli tail events

Nonnegative weighted sums increase when active coordinates are added.  Their
upper tails are therefore increasing events and their lower tails are
decreasing events.  These elementary facts are the polarity input for the
monotone lopsided local lemma.
-/

namespace WeightedEdgeColoring.FiniteBernoulliTailMonotone

open WeightedEdgeColoring.FiniteBernoulliChernoff
open WeightedEdgeColoring.FiniteBernoulliHarris

variable {I : Type*} [Fintype I] [DecidableEq I]

/-- A nonnegative weighted sum is monotone under inclusion of active
coordinates. -/
theorem weightedSum_mono (a : I → ℝ) (ha : ∀ i, 0 ≤ a i)
    {S T : Finset I} (hST : S ⊆ T) :
    weightedSum a S ≤ weightedSum a T := by
  unfold weightedSum
  exact Finset.sum_le_sum_of_subset_of_nonneg hST
    (fun i _hiT _hiS ↦ ha i)

/-- The upper tail of a nonnegative weighted Bernoulli sum is increasing. -/
theorem upperTail_weightedSum_isIncreasing
    (a : I → ℝ) (r : ℝ) (ha : ∀ i, 0 ≤ a i) :
    IsIncreasing (upperTail (weightedSum a) r) := by
  intro S hS T hST
  simp only [upperTail, Finset.mem_filter, Finset.mem_univ, true_and] at hS ⊢
  exact hS.trans (weightedSum_mono a ha hST)

/-- The lower tail of a nonnegative weighted Bernoulli sum is decreasing. -/
theorem lowerTail_weightedSum_isDecreasing
    (a : I → ℝ) (r : ℝ) (ha : ∀ i, 0 ≤ a i) :
    IsDecreasing (lowerTail (weightedSum a) r) := by
  intro T hT S hST
  simp only [lowerTail, Finset.mem_filter, Finset.mem_univ, true_and] at hT ⊢
  exact (weightedSum_mono a ha hST).trans hT

/-- Requiring two fixed coordinates to be active is an increasing event. -/
theorem pair_active_isIncreasing (i j : I) :
    IsIncreasing (Finset.univ.filter fun S : Finset I ↦ i ∈ S ∧ j ∈ S) := by
  intro S hS T hST
  simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hS ⊢
  exact ⟨hST hS.1, hST hS.2⟩

end WeightedEdgeColoring.FiniteBernoulliTailMonotone
