import WeightedEdgeColoring.RankThreeActiveJobs
import WeightedEdgeColoring.RankThreeOptionRestriction
import WeightedEdgeColoring.RankThreeResidualNibble
import WeightedEdgeColoring.WeightedGraph

/-!
# Monotonicity of residual option systems

Passing to a residual system only removes options.  Consequently every
degree and codegree upper bound that holds in the original option system
continues to hold after any accumulated partial matching.  These facts let
an iterated round reuse fixed global parameters without reproving its sparse
codegree hypotheses at every step.
-/

namespace WeightedEdgeColoring.RankThreeOptionSystem

universe u v w

variable {Job : Type u} {Slot : Type v} {Option : Type w}
  [Fintype Job] [Fintype Slot] [Fintype Option]
  [DecidableEq Job] [DecidableEq Slot] [DecidableEq Option]
  (H : RankThreeOptionSystem Job Slot Option)

/-- A residual system is definitionally the option-induced system on the
set of residual options. -/
theorem residualSystem_eq_inducedOnOptions (M : Finset Option) :
    H.residualSystem M = H.inducedOnOptions (H.residualOptions M) := rfl

/-- Taking a residual cannot increase a job fibre. -/
theorem residualSystem_fiber_card_le_original
    (M : Finset Option) (j : Job) :
    ((H.residualSystem M).fiber j).card ≤ (H.fiber j).card := by
  exact H.inducedOnOptions_fiber_card_le (H.residualOptions M) j

/-- Taking a residual cannot increase a slot degree. -/
theorem residualSystem_slotDegree_le_original
    (M : Finset Option) (s : Slot) :
    (H.residualSystem M).slotDegree s ≤ H.slotDegree s := by
  exact H.inducedOnOptions_slotDegree_le (H.residualOptions M) s

/-- Taking a residual cannot increase a job--slot codegree. -/
theorem residualSystem_jobSlotCodegree_le_original
    (M : Finset Option) (j : Job) (s : Slot) :
    (H.residualSystem M).jobSlotCodegree j s ≤
      H.jobSlotCodegree j s := by
  exact H.inducedOnOptions_jobSlotCodegree_le
    (H.residualOptions M) j s

/-- Taking a residual cannot increase a slot-pair codegree. -/
theorem residualSystem_slotPairCodegree_le_original
    (M : Finset Option) (s t : Slot) :
    (H.residualSystem M).slotPairCodegree s t ≤
      H.slotPairCodegree s t := by
  exact H.inducedOnOptions_slotPairCodegree_le
    (H.residualOptions M) s t

/-- Every residual active job was active in the original system. -/
theorem residualSystem_activeJobs_subset_original (M : Finset Option) :
    (H.residualSystem M).activeJobs ⊆ H.activeJobs := by
  intro j hj
  rw [H.mem_activeJobs]
  rcases ((H.residualSystem M).mem_activeJobs j).mp hj with ⟨o, ho⟩
  exact ⟨o.1, H.mem_fiber.mpr
    ((H.residualSystem M).mem_fiber.mp ho)⟩

/-- Fixed global job-degree and sparsity bounds pass simultaneously to every
residual system.  This is the package needed by a later fixed-rate round. -/
theorem residualSystem_global_bounds
    (M : Finset Option) (J S lambda : ℕ)
    (hjobDegree : ∀ j, (H.fiber j).card ≤ J)
    (hslotDegree : ∀ s, H.slotDegree s ≤ S)
    (hjobSlot : ∀ j s, H.jobSlotCodegree j s ≤ lambda)
    (hslotPair : ∀ s t, s ≠ t → H.slotPairCodegree s t ≤ lambda) :
    (∀ j, ((H.residualSystem M).fiber j).card ≤ J) ∧
    (∀ s, (H.residualSystem M).slotDegree s ≤ S) ∧
    (∀ j s, (H.residualSystem M).jobSlotCodegree j s ≤ lambda) ∧
    (∀ s t, s ≠ t →
      (H.residualSystem M).slotPairCodegree s t ≤ lambda) := by
  refine ⟨fun j ↦ (H.residualSystem_fiber_card_le_original M j).trans
      (hjobDegree j),
    fun s ↦ (H.residualSystem_slotDegree_le_original M s).trans
      (hslotDegree s),
    fun j s ↦ (H.residualSystem_jobSlotCodegree_le_original M j s).trans
      (hjobSlot j s), ?_⟩
  intro s t hst
  exact (H.residualSystem_slotPairCodegree_le_original M s t).trans
    (hslotPair s t hst)

/-- The three fixed sparsity bounds, without a job-degree parameter. -/
theorem residualSystem_sparsity_bounds
    (M : Finset Option) (S lambda : ℕ)
    (hslotDegree : ∀ s, H.slotDegree s ≤ S)
    (hjobSlot : ∀ j s, H.jobSlotCodegree j s ≤ lambda)
    (hslotPair : ∀ s t, s ≠ t → H.slotPairCodegree s t ≤ lambda) :
    (∀ s, (H.residualSystem M).slotDegree s ≤ S) ∧
    (∀ j s, (H.residualSystem M).jobSlotCodegree j s ≤ lambda) ∧
    (∀ s t, s ≠ t →
      (H.residualSystem M).slotPairCodegree s t ≤ lambda) := by
  exact ⟨fun s ↦ (H.residualSystem_slotDegree_le_original M s).trans
      (hslotDegree s),
    fun j s ↦ (H.residualSystem_jobSlotCodegree_le_original M j s).trans
      (hjobSlot j s),
    fun s t hst ↦
      (H.residualSystem_slotPairCodegree_le_original M s t).trans
        (hslotPair s t hst)⟩

end WeightedEdgeColoring.RankThreeOptionSystem

namespace WeightedEdgeColoring

universe u v w

/-- A global edge-weight lower bound remains valid when one restricts to the
active jobs of any residual option system. -/
theorem WeightedSimpleGraph.weight_lower_on_residual_activeJobs
    (G : WeightedSimpleGraph.{u})
    {Slot : Type v} {Option : Type w}
    [Fintype Slot] [Fintype Option]
    [DecidableEq Slot] [DecidableEq Option]
    (H : RankThreeOptionSystem G.E Slot Option)
    (M : Finset Option) (β : ℝ)
    (hlower : ∀ e, β ≤ G.weight e) :
    ∀ e ∈ (H.residualSystem M).activeJobs, β ≤ G.weight e := by
  intro e _he
  exact hlower e

end WeightedEdgeColoring
