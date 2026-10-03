import WeightedEdgeColoring.FiniteCategoricalSupportSplit

/-!
# A support-overlap local lemma for arbitrary categorical events

The row selector in `FiniteCategoricalSupportSplit` is tailored to additive
loads.  Some later rounding steps have nonlinear local bad events (for
example, a star statistic or a two-endpoint proposal).  This file records the
same product-space argument for an arbitrary finite family of events.  An
application only has to prove an unconditional probability bound and say
which independent categorical sources each event reads.
-/

namespace WeightedEdgeColoring.FiniteCategoricalEventLLL

open scoped BigOperators

variable {Source State Event : Type*}
variable [Fintype Source] [DecidableEq Source]
variable [Fintype State] [DecidableEq State]
variable [Fintype Event] [DecidableEq Event]

/-- All sources read by a finite family of events. -/
noncomputable def supportsOfEvents
    (support : Event → Finset Source) (T : Finset Event) : Finset Source :=
  T.biUnion support

/-- Other events whose declared source support meets that of `i`. -/
noncomputable def overlapNeighbor
    (support : Event → Finset Source) (i : Event) : Finset Event :=
  Finset.univ.filter fun j ↦
    j ≠ i ∧ (support i ∩ support j).Nonempty

/-- Events whose declared support contains a fixed source. -/
noncomputable def supportIncidence
    (support : Event → Finset Source) (s : Source) : Finset Event :=
  Finset.univ.filter fun i ↦ s ∈ support i

/-- Avoiding events in `T` only reads the union of their declared supports. -/
theorem avoid_dependsOn_supportsOfEvents
    (event : Event → Finset (Source → State))
    (support : Event → Finset Source)
    (hdep : ∀ i,
      WeightedEdgeColoring.FiniteCategoricalSelection.DependsOn (support i) (event i))
    (T : Finset Event) :
    WeightedEdgeColoring.FiniteCategoricalSelection.DependsOn
      (supportsOfEvents support T)
      (WeightedEdgeColoring.FiniteLocalLemma.avoid event T) := by
  intro x y hxy
  simp only [WeightedEdgeColoring.FiniteLocalLemma.avoid, Finset.mem_filter,
    Finset.mem_univ, true_and]
  constructor
  · intro hx i hi hybad
    have hagree : ∀ s ∈ support i, x s = y s := by
      intro s hs
      exact hxy s (Finset.mem_biUnion.mpr ⟨i, hi, hs⟩)
    exact hx i hi ((hdep i x y hagree).mpr hybad)
  · intro hy i hi hxbad
    have hagree : ∀ s ∈ support i, x s = y s := by
      intro s hs
      exact hxy s (Finset.mem_biUnion.mpr ⟨i, hi, hs⟩)
    exact hy i hi ((hdep i x y hagree).mp hxbad)

/-- A non-neighbour family reads sources disjoint from the current event. -/
theorem support_disjoint_supportsOfEvents_of_nonNeighbors
    (support : Event → Finset Source) (i : Event) (T : Finset Event)
    (hT : T ⊆ Finset.univ \ insert i (overlapNeighbor support i)) :
    Disjoint (support i) (supportsOfEvents support T) := by
  rw [Finset.disjoint_left]
  intro s hsi hsT
  rcases Finset.mem_biUnion.mp hsT with ⟨j, hjT, hsj⟩
  have houtside := Finset.mem_sdiff.mp (hT hjT)
  have hji : j ≠ i := by
    intro h
    subst j
    exact houtside.2 (Finset.mem_insert_self i _)
  have hjneighbor : j ∈ overlapNeighbor support i := by
    simp only [overlapNeighbor, Finset.mem_filter, Finset.mem_univ, true_and]
    exact ⟨hji, ⟨s, Finset.mem_inter.mpr ⟨hsi, hsj⟩⟩⟩
  exact houtside.2 (Finset.mem_insert_of_mem hjneighbor)

/-- If every event reads at most `A` sources and every source is read by at
most `B` events, then the support-overlap degree is at most `A * B`. -/
theorem overlapNeighbor_card_le
    (support : Event → Finset Source) (A B : ℕ)
    (hevent : ∀ i, (support i).card ≤ A)
    (hsource : ∀ s, (supportIncidence support s).card ≤ B)
    (i : Event) :
    (overlapNeighbor support i).card ≤ A * B := by
  have hsub : overlapNeighbor support i ⊆
      (support i).biUnion (supportIncidence support) := by
    intro j hj
    have hmeet : (support i ∩ support j).Nonempty :=
      (Finset.mem_filter.mp hj).2.2
    rcases hmeet with ⟨s, hs⟩
    have hsi : s ∈ support i := (Finset.mem_inter.mp hs).1
    have hsj : s ∈ support j := (Finset.mem_inter.mp hs).2
    exact Finset.mem_biUnion.mpr ⟨s, hsi,
      Finset.mem_filter.mpr ⟨Finset.mem_univ j, hsj⟩⟩
  calc
    (overlapNeighbor support i).card ≤
        ((support i).biUnion (supportIncidence support)).card :=
      Finset.card_le_card hsub
    _ ≤ ∑ s ∈ support i, (supportIncidence support s).card :=
      Finset.card_biUnion_le
    _ ≤ ∑ _s ∈ support i, B := by
      exact Finset.sum_le_sum fun s _ ↦ hsource s
    _ = (support i).card * B := by simp
    _ ≤ A * B := Nat.mul_le_mul_right B (hevent i)

/-- Symmetric lopsided local lemma for arbitrary events in a finite
categorical product.  Disjoint declared supports supply exact independence,
so the application-facing hypotheses are only a support declaration, an
unconditional event-mass bound, and the usual numerical inequality. -/
theorem exists_avoids_of_support_overlap
    (prob : Source → State → ℝ)
    (event : Event → Finset (Source → State))
    (support : Event → Finset Source)
    (p x : ℝ) (d : ℕ)
    (hprob0 : ∀ s a, 0 ≤ prob s a)
    (hprobSum : ∀ s, ∑ a, prob s a = 1)
    (hdep : ∀ i,
      WeightedEdgeColoring.FiniteCategoricalSelection.DependsOn (support i) (event i))
    (hdegree : ∀ i, (overlapNeighbor support i).card ≤ d)
    (hx0 : 0 ≤ x) (hx1 : x < 1)
    (hnumeric : p ≤ x * (1 - x) ^ d)
    (hbad : ∀ i,
      WeightedEdgeColoring.FiniteLocalLemma.eventMass
        (WeightedEdgeColoring.FiniteCategoricalSelection.categoricalMass prob)
        (event i) ≤ p) :
    ∃ choice : Source → State, ∀ i, choice ∉ event i := by
  have hpositive :
      0 < WeightedEdgeColoring.FiniteLocalLemma.eventMass
        (WeightedEdgeColoring.FiniteCategoricalSelection.categoricalMass prob)
        (WeightedEdgeColoring.FiniteLocalLemma.avoid event Finset.univ) := by
    apply WeightedEdgeColoring.FiniteProductCylinder.symmetric_lopsided_local_lemma_of_independent
      (WeightedEdgeColoring.FiniteCategoricalSelection.categoricalMass prob)
      event (overlapNeighbor support) p x d
      (WeightedEdgeColoring.FiniteCategoricalSelection.categoricalMass_nonneg prob hprob0)
      (WeightedEdgeColoring.FiniteCategoricalSelection.sum_categoricalMass prob hprobSum)
      hdegree hx0 hx1 hnumeric hbad
    intro i T hT
    apply WeightedEdgeColoring.FiniteCategoricalSupportSplit.independentEvents_of_dependsOn_disjoint
      prob hprobSum (support i) (supportsOfEvents support T)
    · exact support_disjoint_supportsOfEvents_of_nonNeighbors support i T hT
    · exact hdep i
    · exact avoid_dependsOn_supportsOfEvents event support hdep T
  have hnonempty :
      (WeightedEdgeColoring.FiniteLocalLemma.avoid event Finset.univ).Nonempty := by
    by_contra hempty
    rw [Finset.not_nonempty_iff_eq_empty.mp hempty] at hpositive
    simp [WeightedEdgeColoring.FiniteLocalLemma.eventMass] at hpositive
  obtain ⟨choice, hchoice⟩ := hnonempty
  refine ⟨choice, ?_⟩
  intro i
  have hall := hchoice
  simp only [WeightedEdgeColoring.FiniteLocalLemma.avoid, Finset.mem_filter,
    Finset.mem_univ, true_and] at hall
  exact hall i trivial

end WeightedEdgeColoring.FiniteCategoricalEventLLL
