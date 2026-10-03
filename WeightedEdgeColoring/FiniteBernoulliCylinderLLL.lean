import WeightedEdgeColoring.FiniteBernoulliSupportedLLL

/-!
# Local lemma for Bernoulli cylinder events with disjoint supports

An event supported on `L` can be viewed as an outside event relative to `K`
whenever `K` and `L` are disjoint.  This observation removes the remaining
representation premise from the supported-event local lemma: applications
only specify each event's support and prove that non-neighbor supports are
disjoint.
-/

namespace WeightedEdgeColoring.FiniteBernoulliSupportSplit

open scoped BigOperators

variable {I J : Type*}
  [Fintype I] [DecidableEq I] [Fintype J] [DecidableEq J]

/-- Replace the coordinates in `K` by the empty outcome while retaining a
given outside outcome. -/
noncomputable def zeroInsideExtension (K : Finset I)
    (B : Finset (Outside K)) : Finset I :=
  (splitEquiv K).symm (∅, B)

/-- The view, from outside `K`, of an event originally supported on `L`. -/
noncomputable def outsideView (K L : Finset I)
    (event : Finset (Finset (Inside L))) : Finset (Finset (Outside K)) :=
  Finset.univ.filter fun B ↦
    (splitEquiv L (zeroInsideExtension K B)).1 ∈ event

/-- Zeroing coordinates in `K` does not change the coordinates in a disjoint
set `L`. -/
theorem insideProjection_zeroInsideExtension
    (K L : Finset I) (hKL : Disjoint K L) (S : Finset I) :
    (splitEquiv L S).1 =
      (splitEquiv L
        (zeroInsideExtension K (splitEquiv K S).2)).1 := by
  ext i
  simp only [mem_splitEquiv_inside]
  have hiK : (i : I) ∉ K := by
    intro hi
    exact Finset.disjoint_left.mp hKL hi i.2
  let io : Outside K := ⟨i, hiK⟩
  calc
    (i : I) ∈ S ↔ io ∈ (splitEquiv K S).2 :=
      (mem_splitEquiv_outside K S io).symm
    _ ↔ io ∈ (splitEquiv K
        (zeroInsideExtension K (splitEquiv K S).2)).2 := by
      simp [zeroInsideExtension]
    _ ↔ (i : I) ∈ zeroInsideExtension K (splitEquiv K S).2 :=
      mem_splitEquiv_outside K _ io

/-- A cylinder on `L` is an outside cylinder relative to every disjoint
support `K`. -/
theorem insideCylinder_eq_outsideCylinder_of_disjoint
    (K L : Finset I) (hKL : Disjoint K L)
    (event : Finset (Finset (Inside L))) :
    insideCylinder L event = outsideCylinder K (outsideView K L event) := by
  ext S
  simp only [mem_insideCylinder, mem_outsideCylinder, outsideView,
    Finset.mem_filter, Finset.mem_univ, true_and]
  rw [insideProjection_zeroInsideExtension K L hKL S]

/-- Symmetric lopsided LLL for cylinder events.  It is enough that every
non-neighbor has disjoint coordinate support. -/
theorem symmetric_lopsided_local_lemma_of_disjoint_supports
    (q : I → ℝ)
    (support : J → Finset I)
    (localBad : (j : J) → Finset (Finset (Inside (support j))))
    (neighbor : J → Finset J)
    (p x : ℝ) (d : ℕ)
    (hq_nonneg : ∀ i, 0 ≤ q i) (hq_le_one : ∀ i, q i ≤ 1)
    (hdegree : ∀ j, (neighbor j).card ≤ d)
    (hx_nonneg : 0 ≤ x) (hx_lt_one : x < 1)
    (hnumeric : p ≤ x * (1 - x) ^ d)
    (hdisjoint : ∀ j i, i ∉ insert j (neighbor j) →
      Disjoint (support j) (support i))
    (hlocal : ∀ j,
      WeightedEdgeColoring.FiniteLocalLemma.eventMass
        (WeightedEdgeColoring.FiniteBernoulliChernoff.bernoulliMass
          (insideParameter q (support j))) (localBad j) ≤ p) :
    0 < WeightedEdgeColoring.FiniteLocalLemma.eventMass
      (WeightedEdgeColoring.FiniteBernoulliChernoff.bernoulliMass q)
      (WeightedEdgeColoring.FiniteLocalLemma.avoid
        (fun j ↦ insideCylinder (support j) (localBad j)) Finset.univ) := by
  let outsideBad : (j : J) → J →
      Finset (Finset (Outside (support j))) :=
    fun j i ↦ outsideView (support j) (support i) (localBad i)
  apply symmetric_lopsided_local_lemma_of_supported_events
    q (fun j ↦ insideCylinder (support j) (localBad j))
    support localBad outsideBad neighbor p x d
    hq_nonneg hq_le_one hdegree hx_nonneg hx_lt_one hnumeric
  · intro j
    rfl
  · intro j i hi
    exact insideCylinder_eq_outsideCylinder_of_disjoint
      (support j) (support i) (hdisjoint j i hi) (localBad i)
  · exact hlocal

end WeightedEdgeColoring.FiniteBernoulliSupportSplit
