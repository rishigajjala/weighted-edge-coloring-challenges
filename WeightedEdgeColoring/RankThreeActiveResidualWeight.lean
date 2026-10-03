import WeightedEdgeColoring.RankThreeEndpointGroupRound
import WeightedEdgeColoring.RankThreeResidualComposition

/-!
# Active jobs and the weight left after a residual round

The Harris round is run only on jobs whose current fibre is nonempty.  This
file records the simple fact that, while the protected job loss is smaller
than the current lower degree, the active jobs after the round are exactly
the formerly active jobs that were not covered.  It then turns a weighted
coverage guarantee into a one-step recurrence for the active star weight.
-/

open scoped BigOperators

namespace WeightedEdgeColoring
namespace RankThreeOptionSystem

universe u v w

variable {Job : Type u} {Slot : Type v} {Option : Type w}
  [Fintype Job] [Fintype Slot] [Fintype Option]
  [DecidableEq Job] [DecidableEq Slot] [DecidableEq Option]
  (H : RankThreeOptionSystem Job Slot Option)

/-- The empty residual system has exactly the original active jobs. -/
theorem residualSystem_empty_activeJobs :
    (H.residualSystem ∅).activeJobs = H.activeJobs := by
  ext j
  rw [(H.residualSystem ∅).mem_activeJobs, H.mem_activeJobs]
  constructor
  · rintro ⟨q, hq⟩
    exact ⟨q.1, H.mem_fiber.mpr
      ((H.residualSystem ∅).mem_fiber.mp hq)⟩
  · rintro ⟨o, ho⟩
    have hores : o ∈ H.residualOptions ∅ := by simp
    let q : H.ResidualOption ∅ := ⟨o, hores⟩
    exact ⟨q, (H.residualSystem ∅).mem_fiber.mpr (H.mem_fiber.mp ho)⟩

/-- Coverage by an accumulated matching plus a lifted residual matching is
the disjunction of coverage in the two rounds. -/
theorem covers_union_liftResidualSet_iff
    (M : Finset Option) (A : Finset (H.ResidualOption M)) (j : Job) :
    H.Covers (M ∪ H.liftResidualSet M A) j ↔
      H.Covers M j ∨ (H.residualSystem M).Covers A j := by
  constructor
  · rintro ⟨p, hp, hpowner⟩
    rcases Finset.mem_union.mp hp with hpM | hpA
    · exact Or.inl ⟨p, hpM, hpowner⟩
    · rcases H.mem_liftResidualSet.mp hpA with ⟨q, hqA, rfl⟩
      exact Or.inr ⟨q, hqA, hpowner⟩
  · rintro (⟨p, hpM, hpowner⟩ | ⟨q, hqA, hqowner⟩)
    · exact ⟨p, Finset.mem_union_left _ hpM, hpowner⟩
    · exact ⟨q.1, Finset.mem_union_right _
          (H.mem_liftResidualSet.mpr ⟨q, hqA, rfl⟩), hqowner⟩

/-- If an uncovered active job loses fewer options than its protected lower
degree, then it remains active.  Conversely, every residual active job was
active and was not covered. -/
theorem residual_activeJobs_eq_filter_of_job_loss
    (A : Finset Option) (d U : ℕ)
    (hlower : ∀ o, d ≤ (H.fiber (H.owner o)).card)
    (hjob : ∀ j, ¬ H.Covers A j →
      H.residualJobDegree ∅ j ≤ H.residualJobDegree A j + U)
    (hUd : U < d) :
    (H.residualSystem A).activeJobs =
      H.activeJobs.filter fun j ↦ ¬ H.Covers A j := by
  ext j
  simp only [Finset.mem_filter]
  constructor
  · intro hj
    rcases ((H.residualSystem A).mem_activeJobs j).mp hj with ⟨q, hq⟩
    have howner : H.owner q.1 = j :=
      (H.residualSystem A).mem_fiber.mp hq
    have hactive : j ∈ H.activeJobs := by
      rw [H.mem_activeJobs]
      exact ⟨q.1, H.mem_fiber.mpr howner⟩
    have hnot : ¬ H.Covers A j := by
      rintro ⟨p, hp, hpowner⟩
      have hres := H.mem_residualOptions.mp q.2 p hp
      exact hres.1 (howner.trans hpowner.symm)
    exact ⟨hactive, hnot⟩
  · rintro ⟨hactive, hnot⟩
    have hlowerj : d ≤ (H.fiber j).card :=
      H.fiber_card_ge_of_mem_activeJobs d hlower hactive
    have hj := hjob j hnot
    have hempty : H.residualJobDegree ∅ j = (H.fiber j).card := by
      unfold residualJobDegree residualFiber residualOptions fiber
      simp
    rw [hempty] at hj
    have hpos : 0 < H.residualJobDegree A j := by omega
    rw [(H.residualSystem A).mem_activeJobs]
    rw [← Finset.card_pos, H.residualSystem_fiber_card]
    exact hpos

/-- The active-job identity transported through the canonical equivalence
between a residual of a residual and the residual after the lifted union. -/
theorem residual_union_activeJobs_eq_filter_of_job_loss
    (M : Finset Option) (A : Finset (H.ResidualOption M)) (d U : ℕ)
    (hlower : ∀ o : H.ResidualOption M,
      d ≤ (((H.residualSystem M).fiber
        ((H.residualSystem M).owner o)).card))
    (hjob : ∀ j, ¬ (H.residualSystem M).Covers A j →
      (H.residualSystem M).residualJobDegree ∅ j ≤
        (H.residualSystem M).residualJobDegree A j + U)
    (hUd : U < d) :
    (H.residualSystem (M ∪ H.liftResidualSet M A)).activeJobs =
      (H.residualSystem M).activeJobs.filter fun j ↦
        ¬ (H.residualSystem M).Covers A j := by
  let R := H.residualSystem M
  have hnested := R.residual_activeJobs_eq_filter_of_job_loss
    A d U hlower hjob hUd
  rw [← hnested]
  ext j
  rw [(H.residualSystem (M ∪ H.liftResidualSet M A)).mem_activeJobs,
    (R.residualSystem A).mem_activeJobs]
  rw [← Finset.card_pos, ← Finset.card_pos]
  rw [H.residualSystem_union_fiber_card M A j]

/-- If the current active set already equals the original uncovered active
jobs, the equality persists after a protected residual round. -/
theorem residual_union_activeJobs_eq_original_filter
    (M : Finset Option) (A : Finset (H.ResidualOption M)) (d U : ℕ)
    (hactive : (H.residualSystem M).activeJobs =
      H.activeJobs.filter fun j ↦ ¬ H.Covers M j)
    (hlower : ∀ o : H.ResidualOption M,
      d ≤ (((H.residualSystem M).fiber
        ((H.residualSystem M).owner o)).card))
    (hjob : ∀ j, ¬ (H.residualSystem M).Covers A j →
      (H.residualSystem M).residualJobDegree ∅ j ≤
        (H.residualSystem M).residualJobDegree A j + U)
    (hUd : U < d) :
    (H.residualSystem (M ∪ H.liftResidualSet M A)).activeJobs =
      H.activeJobs.filter fun j ↦
        ¬ H.Covers (M ∪ H.liftResidualSet M A) j := by
  rw [H.residual_union_activeJobs_eq_filter_of_job_loss
    M A d U hlower hjob hUd, hactive]
  ext j
  simp only [Finset.mem_filter]
  rw [H.covers_union_liftResidualSet_iff M A j]
  tauto

end RankThreeOptionSystem

namespace WeightedSimpleGraph

universe u v w

variable (G : WeightedSimpleGraph.{u})
  {Slot : Type v} {Option : Type w}
  [Fintype Slot] [Fintype Option]
  [DecidableEq Slot] [DecidableEq Option]
  (H : RankThreeOptionSystem G.E Slot Option)

/-- Weight of the currently active incident jobs at one vertex. -/
noncomputable def residualActiveStarWeight (M : Finset Option) (vtx : G.V) : ℝ :=
  ∑ e ∈ G.activeStarEdgeSet (H.residualSystem M).activeJobs vtx, G.weight e

/-- Weight of the originally active incident jobs not covered by `M`. -/
noncomputable def uncoveredActiveStarWeight
    (M : Finset Option) (vtx : G.V) : ℝ :=
  ∑ e ∈ (G.activeStarEdgeSet H.activeJobs vtx).filter
    (fun e ↦ ¬ H.Covers M e), G.weight e

/-- Once active-job persistence is known, the residual active-star weight is
exactly the weight of the originally active jobs left uncovered. -/
theorem residualActiveStarWeight_eq_uncoveredActiveStarWeight
    (M : Finset Option)
    (hactive : (H.residualSystem M).activeJobs =
      H.activeJobs.filter fun j ↦ ¬ H.Covers M j)
    (vtx : G.V) :
    G.residualActiveStarWeight H M vtx =
      G.uncoveredActiveStarWeight H M vtx := by
  classical
  unfold residualActiveStarWeight uncoveredActiveStarWeight
  rw [hactive]
  congr 1
  ext e
  simp only [G.mem_activeStarEdgeSet, Finset.mem_filter]
  tauto

/-- Exact active-star accounting for one residual round. -/
theorem residualActiveStarWeight_union_add_covered
    (M : Finset Option) (A : Finset (H.ResidualOption M))
    (d U : ℕ)
    (hlower : ∀ o : H.ResidualOption M,
      d ≤ (((H.residualSystem M).fiber
        ((H.residualSystem M).owner o)).card))
    (hjob : ∀ j, ¬ (H.residualSystem M).Covers A j →
      (H.residualSystem M).residualJobDegree ∅ j ≤
        (H.residualSystem M).residualJobDegree A j + U)
    (hUd : U < d) (vtx : G.V) :
    G.residualActiveStarWeight H (M ∪ H.liftResidualSet M A) vtx +
        (∑ e ∈ (G.activeStarEdgeSet
          (H.residualSystem M).activeJobs vtx).filter
            ((H.residualSystem M).Covers A), G.weight e) =
      G.residualActiveStarWeight H M vtx := by
  classical
  have hactive := H.residual_union_activeJobs_eq_filter_of_job_loss
    M A d U hlower hjob hUd
  unfold residualActiveStarWeight
  rw [hactive]
  have hset :
      G.activeStarEdgeSet
          ((H.residualSystem M).activeJobs.filter fun j ↦
            ¬ (H.residualSystem M).Covers A j) vtx =
        (G.activeStarEdgeSet (H.residualSystem M).activeJobs vtx).filter
          (fun j ↦ ¬ (H.residualSystem M).Covers A j) := by
    ext e
    simp only [mem_activeStarEdgeSet, Finset.mem_filter]
    constructor
    · rintro ⟨⟨hactive, hnot⟩, hinc⟩
      exact ⟨⟨hactive, hinc⟩, hnot⟩
    · rintro ⟨⟨hactive, hinc⟩, hnot⟩
      exact ⟨⟨hactive, hnot⟩, hinc⟩
  rw [hset]
  simpa [add_comm] using
    (Finset.sum_filter_add_sum_filter_not
      (s := G.activeStarEdgeSet (H.residualSystem M).activeJobs vtx)
      (p := fun e ↦ (H.residualSystem M).Covers A e)
      (f := G.weight))

/-- A coverage gain on the current active star gives the affine one-step
recurrence used by the geometric iteration. -/
theorem residualActiveStarWeight_union_le
    (M : Finset Option) (A : Finset (H.ResidualOption M))
    (d U : ℕ) (theta floor : ℝ)
    (hlower : ∀ o : H.ResidualOption M,
      d ≤ (((H.residualSystem M).fiber
        ((H.residualSystem M).owner o)).card))
    (hjob : ∀ j, ¬ (H.residualSystem M).Covers A j →
      (H.residualSystem M).residualJobDegree ∅ j ≤
        (H.residualSystem M).residualJobDegree A j + U)
    (hUd : U < d) (_htheta0 : 0 ≤ theta)
    (hgain : ∀ vtx,
      theta * (G.residualActiveStarWeight H M vtx - floor) ≤
        ∑ e ∈ (G.activeStarEdgeSet
          (H.residualSystem M).activeJobs vtx).filter
            ((H.residualSystem M).Covers A), G.weight e) :
    ∀ vtx,
      G.residualActiveStarWeight H (M ∪ H.liftResidualSet M A) vtx ≤
        (1 - theta) * G.residualActiveStarWeight H M vtx + theta * floor := by
  intro vtx
  have haccount := G.residualActiveStarWeight_union_add_covered
    H M A d U hlower hjob hUd vtx
  have hgain := hgain vtx
  nlinarith

end WeightedSimpleGraph
end WeightedEdgeColoring
