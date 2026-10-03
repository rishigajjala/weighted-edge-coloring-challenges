import WeightedEdgeColoring.BoundedMultiplicityDyadicOptions
import WeightedEdgeColoring.PartialCompletion
import WeightedEdgeColoring.RankThreeJobRestriction

/-!
# Large-edge job restriction for weighted multigraphs

The selected-profile endpoint iteration is run only on jobs whose edge weight
is at least `beta`.  This file ports that graph-facing restriction layer to
`WeightedMultigraph`, including preservation of endpoint multiplicity and the
degree/codegree facts needed by the rank-three engine.
-/

namespace WeightedEdgeColoring

noncomputable section

namespace WeightedMultigraph

universe u v w

variable (G : WeightedMultigraph.{u})

/-- Edges whose weight is at least `beta`. -/
def largeEdgeJobs (beta : ℝ) : Finset G.E :=
  Finset.univ.filter fun e ↦ beta ≤ G.weight e

@[simp] theorem mem_largeEdgeJobs {beta : ℝ} {e : G.E} :
    e ∈ G.largeEdgeJobs beta ↔ beta ≤ G.weight e := by
  simp [largeEdgeJobs]

/-- The weighted multigraph restricted to its `beta`-large indexed edges. -/
abbrev largeEdgeRestriction (beta : ℝ) : WeightedMultigraph :=
  G.edgeRestriction (G.largeEdgeJobs beta)

theorem largeEdgeRestriction_weight_lower (beta : ℝ)
    (e : (G.largeEdgeRestriction beta).E) :
    beta ≤ (G.largeEdgeRestriction beta).weight e := by
  exact G.mem_largeEdgeJobs.mp e.2

/-- Restriction of the indexed edge set cannot increase endpoint-pair
multiplicity. -/
theorem edgeRestriction_pairMultiplicityAtMost
    {L : ℕ} (hmult : G.PairMultiplicityAtMost L) (R : Finset G.E) :
    (G.edgeRestriction R).PairMultiplicityAtMost L := by
  intro u v
  let F : Finset (G.edgeRestriction R).E :=
    (G.edgeRestriction R).endpointPairCell u v
  let B : Finset G.E := Finset.univ.filter (G.EndpointPairMatches u v)
  have hmaps : (F : Set (G.edgeRestriction R).E).MapsTo
      Subtype.val B := by
    intro e he
    have hematch : (G.edgeRestriction R).EndpointPairMatches u v e :=
      ((G.edgeRestriction R).mem_endpointPairCell_iff_endpointPairMatches
        u v e).mp he
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_univ _, ?_⟩
    simpa [EndpointPairMatches] using hematch
  have hcard : F.card ≤ B.card :=
    Finset.card_le_card_of_injOn Subtype.val hmaps
      (Set.injOn_of_injective Subtype.val_injective)
  have hB : B.card ≤ L := by
    exact G.endpointPairMatches_card_le hmult u v
  change F.card ≤ L
  exact hcard.trans hB

theorem largeEdgeRestriction_pairMultiplicityAtMost
    {L : ℕ} (hmult : G.PairMultiplicityAtMost L) (beta : ℝ) :
    (G.largeEdgeRestriction beta).PairMultiplicityAtMost L :=
  G.edgeRestriction_pairMultiplicityAtMost hmult (G.largeEdgeJobs beta)

variable {Slot : Type v} {Option : Type w}
  [Fintype Slot] [Fintype Option]
  [DecidableEq Slot] [DecidableEq Option]
  (H : RankThreeOptionSystem G.E Slot Option)

/-- Restrict an option system to the large multigraph jobs. -/
abbrev largeEdgeJobSystem (beta : ℝ) :=
  H.inducedOnJobs (G.largeEdgeJobs beta)

/-- Forget the large-owner proof on a selected option set. -/
abbrev liftLargeEdgeJobSet (beta : ℝ)
    (A : Finset (H.ActiveJobOption (G.largeEdgeJobs beta))) : Finset Option :=
  H.liftActiveJobSet (G.largeEdgeJobs beta) A

theorem liftLargeEdgeJobSet_isPartialMatching
    (beta : ℝ)
    {A : Finset (H.ActiveJobOption (G.largeEdgeJobs beta))}
    (hA : (G.largeEdgeJobSystem H beta).IsPartialMatching A) :
    H.IsPartialMatching (G.liftLargeEdgeJobSet H beta A) := by
  exact H.liftActiveJobSet_isPartialMatching (G.largeEdgeJobs beta) hA

theorem covers_liftLargeEdgeJobSet_iff
    (beta : ℝ)
    (A : Finset (H.ActiveJobOption (G.largeEdgeJobs beta)))
    (e : (G.largeEdgeRestriction beta).E) :
    H.Covers (G.liftLargeEdgeJobSet H beta A) e.1 ↔
      (G.largeEdgeJobSystem H beta).Covers A e := by
  exact H.covers_liftActiveJobSet_iff (G.largeEdgeJobs beta) A e

theorem owner_large_of_mem_liftLargeEdgeJobSet
    {beta : ℝ}
    {A : Finset (H.ActiveJobOption (G.largeEdgeJobs beta))}
    {o : Option} (ho : o ∈ G.liftLargeEdgeJobSet H beta A) :
    beta ≤ G.weight (H.owner o) := by
  rcases H.mem_liftActiveJobSet.mp ho with ⟨q, _hq, rfl⟩
  exact G.mem_largeEdgeJobs.mp q.2

theorem largeEdgeJobSystem_fiber_card (beta : ℝ)
    (e : (G.largeEdgeRestriction beta).E) :
    ((G.largeEdgeJobSystem H beta).fiber e).card =
      (H.fiber e.1).card := by
  exact H.inducedOnJobs_fiber_card (G.largeEdgeJobs beta) e

theorem largeEdgeJobSystem_slotDegree_le (beta : ℝ) (s : Slot) :
    (G.largeEdgeJobSystem H beta).slotDegree s ≤ H.slotDegree s := by
  exact H.inducedOnJobs_slotDegree_le (G.largeEdgeJobs beta) s

theorem largeEdgeJobSystem_jobSlotCodegree (beta : ℝ)
    (e : (G.largeEdgeRestriction beta).E) (s : Slot) :
    (G.largeEdgeJobSystem H beta).jobSlotCodegree e s =
      H.jobSlotCodegree e.1 s := by
  exact H.inducedOnJobs_jobSlotCodegree (G.largeEdgeJobs beta) e s

theorem largeEdgeJobSystem_slotPairCodegree_le
    (beta : ℝ) (s t : Slot) :
    (G.largeEdgeJobSystem H beta).slotPairCodegree s t ≤
      H.slotPairCodegree s t := by
  exact H.inducedOnJobs_slotPairCodegree_le (G.largeEdgeJobs beta) s t

/-- Package the five structural inputs transferred to the restricted job
system.  This is the direct boundary consumed by the closed rank-three
iteration. -/
theorem largeEdgeJobSystem_initialBounds
    (beta : ℝ) (d0 S0 lambda : ℕ)
    (htwo : ∀ o, (H.slots o).card = 2)
    (hdegree : ∀ e ∈ G.largeEdgeJobs beta, d0 ≤ (H.fiber e).card)
    (hslot : ∀ s, H.slotDegree s ≤ S0)
    (hjobSlot : ∀ e s, H.jobSlotCodegree e s ≤ lambda)
    (hslotPair : ∀ s t, s ≠ t → H.slotPairCodegree s t ≤ lambda) :
    (∀ o, ((G.largeEdgeJobSystem H beta).slots o).card = 2) ∧
    (∀ e, d0 ≤ ((G.largeEdgeJobSystem H beta).fiber e).card) ∧
    (∀ s, (G.largeEdgeJobSystem H beta).slotDegree s ≤ S0) ∧
    (∀ e s, (G.largeEdgeJobSystem H beta).jobSlotCodegree e s ≤ lambda) ∧
    (∀ s t, s ≠ t →
      (G.largeEdgeJobSystem H beta).slotPairCodegree s t ≤ lambda) := by
  refine ⟨fun o ↦ htwo o.1, ?_, ?_, ?_, ?_⟩
  · intro e
    rw [H.inducedOnJobs_fiber_card (G.largeEdgeJobs beta)]
    exact hdegree e.1 e.2
  · intro s
    exact (G.largeEdgeJobSystem_slotDegree_le H beta s).trans (hslot s)
  · intro e s
    rw [G.largeEdgeJobSystem_jobSlotCodegree H beta e s]
    exact hjobSlot e.1 s
  · intro s t hst
    exact (G.largeEdgeJobSystem_slotPairCodegree_le H beta s t).trans
      (hslotPair s t hst)

end WeightedMultigraph

end

end WeightedEdgeColoring
