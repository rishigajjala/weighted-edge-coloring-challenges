import WeightedEdgeColoring.FiniteBernoulliSupportSplit

/-!
# A supported-event Bernoulli local lemma

This file combines the exact inside/outside coordinate split with the finite
symmetric lopsided local lemma.  An application supplies, for each bad event,
its finite coordinate support and a local description.  Every non-neighbor
must be described using only coordinates outside that support.  The theorem
then reduces all conditional probability estimates to unconditional local
event bounds.
-/

namespace WeightedEdgeColoring.FiniteBernoulliSupportSplit

open scoped BigOperators

variable {I J : Type*}
  [Fintype I] [DecidableEq I] [Fintype J] [DecidableEq J]

/-- Symmetric lopsided LLL for Bernoulli bad events with explicit disjoint
coordinate supports. -/
theorem symmetric_lopsided_local_lemma_of_supported_events
    (q : I → ℝ)
    (bad : J → Finset (Finset I))
    (support : J → Finset I)
    (localBad : (j : J) → Finset (Finset (Inside (support j))))
    (outsideBad : (j : J) → J → Finset (Finset (Outside (support j))))
    (neighbor : J → Finset J)
    (p x : ℝ) (d : ℕ)
    (hq_nonneg : ∀ i, 0 ≤ q i) (hq_le_one : ∀ i, q i ≤ 1)
    (hdegree : ∀ j, (neighbor j).card ≤ d)
    (hx_nonneg : 0 ≤ x) (hx_lt_one : x < 1)
    (hnumeric : p ≤ x * (1 - x) ^ d)
    (hinside : ∀ j, bad j = insideCylinder (support j) (localBad j))
    (houtside : ∀ j i, i ∉ insert j (neighbor j) →
      bad i = outsideCylinder (support j) (outsideBad j i))
    (hlocal : ∀ j,
      WeightedEdgeColoring.FiniteLocalLemma.eventMass
        (WeightedEdgeColoring.FiniteBernoulliChernoff.bernoulliMass
          (insideParameter q (support j))) (localBad j) ≤ p) :
    0 < WeightedEdgeColoring.FiniteLocalLemma.eventMass
      (WeightedEdgeColoring.FiniteBernoulliChernoff.bernoulliMass q)
      (WeightedEdgeColoring.FiniteLocalLemma.avoid bad Finset.univ) := by
  apply WeightedEdgeColoring.FiniteLocalLemma.symmetric_lopsided_local_lemma
    (WeightedEdgeColoring.FiniteBernoulliChernoff.bernoulliMass q)
    bad neighbor p x d
    (WeightedEdgeColoring.FiniteBernoulliChernoff.bernoulliMass_nonneg
      q hq_nonneg hq_le_one)
    (WeightedEdgeColoring.FiniteBernoulliChernoff.sum_bernoulliMass q)
    hdegree hx_nonneg hx_lt_one hnumeric
  intro j T hT
  have havoid :
      WeightedEdgeColoring.FiniteLocalLemma.avoid bad T =
        WeightedEdgeColoring.FiniteLocalLemma.avoid
          (fun i ↦ outsideCylinder (support j) (outsideBad j i)) T := by
    ext S
    simp only [WeightedEdgeColoring.FiniteLocalLemma.avoid, Finset.mem_filter,
      Finset.mem_univ, true_and]
    constructor
    · intro h i hi
      have hiOutside : i ∉ insert j (neighbor j) :=
        (Finset.mem_sdiff.mp (hT hi)).2
      rw [← houtside j i hiOutside]
      exact h i hi
    · intro h i hi
      have hiOutside : i ∉ insert j (neighbor j) :=
        (Finset.mem_sdiff.mp (hT hi)).2
      rw [houtside j i hiOutside]
      exact h i hi
  rw [hinside j, havoid]
  exact conditional_le_avoid_outsideCylinders
    q (support j) (localBad j) (outsideBad j) T p
    hq_nonneg hq_le_one (hlocal j)

end WeightedEdgeColoring.FiniteBernoulliSupportSplit
