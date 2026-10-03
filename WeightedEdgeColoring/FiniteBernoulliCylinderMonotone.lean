import WeightedEdgeColoring.FiniteBernoulliSupportSplit
import WeightedEdgeColoring.FiniteBernoulliHarris

/-!
# Monotone Bernoulli cylinder events

Projection to a coordinate block preserves inclusion.  Hence lifting a local
increasing or decreasing event to the full Bernoulli product preserves its
polarity.
-/

namespace WeightedEdgeColoring.FiniteBernoulliCylinderMonotone

open WeightedEdgeColoring.FiniteBernoulliHarris
open WeightedEdgeColoring.FiniteBernoulliSupportSplit

variable {I : Type*} [Fintype I] [DecidableEq I]

theorem splitEquiv_inside_mono (K : Finset I) {S T : Finset I}
    (hST : S ⊆ T) :
    (splitEquiv K S).1 ⊆ (splitEquiv K T).1 := by
  intro i hi
  rw [mem_splitEquiv_inside] at hi ⊢
  exact hST hi

theorem splitEquiv_outside_mono (K : Finset I) {S T : Finset I}
    (hST : S ⊆ T) :
    (splitEquiv K S).2 ⊆ (splitEquiv K T).2 := by
  intro i hi
  rw [mem_splitEquiv_outside] at hi ⊢
  exact hST hi

theorem insideCylinder_isIncreasing (K : Finset I)
    (E : Finset (Finset (Inside K))) (hE : IsIncreasing E) :
    IsIncreasing (insideCylinder K E) := by
  intro S hS T hST
  rw [mem_insideCylinder] at hS ⊢
  exact hE hS (splitEquiv_inside_mono K hST)

theorem insideCylinder_isDecreasing (K : Finset I)
    (E : Finset (Finset (Inside K))) (hE : IsDecreasing E) :
    IsDecreasing (insideCylinder K E) := by
  intro T hT S hST
  rw [mem_insideCylinder] at hT ⊢
  exact hE hT (splitEquiv_inside_mono K hST)

theorem outsideCylinder_isIncreasing (K : Finset I)
    (E : Finset (Finset (Outside K))) (hE : IsIncreasing E) :
    IsIncreasing (outsideCylinder K E) := by
  intro S hS T hST
  rw [mem_outsideCylinder] at hS ⊢
  exact hE hS (splitEquiv_outside_mono K hST)

theorem outsideCylinder_isDecreasing (K : Finset I)
    (E : Finset (Finset (Outside K))) (hE : IsDecreasing E) :
    IsDecreasing (outsideCylinder K E) := by
  intro T hT S hST
  rw [mem_outsideCylinder] at hT ⊢
  exact hE hT (splitEquiv_outside_mono K hST)

end WeightedEdgeColoring.FiniteBernoulliCylinderMonotone
