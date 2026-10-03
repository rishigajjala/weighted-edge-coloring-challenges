import WeightedEdgeColoring.RankThreeRegularExtensionBridge
import WeightedEdgeColoring.RankThreeSharpFixedSlackRound
import WeightedEdgeColoring.RankThreeResidualInvariantStep
import WeightedEdgeColoring.RankThreeGroupCoverageBridge

/-!
# Projecting a sharp round through a regular extension

This file contains the last deterministic step of a regularized nibble.
Groups of old jobs are lifted along the job embedding.  A matching in the
regular extension is then pulled back to the old options, while the next old
system keeps exactly the old options which survived in the extension.

The key point for iteration is asymmetric.  Every old job degree is
preserved **exactly** by projection, whereas every old slot degree is at
most its extension residual degree.  Used extension slots have residual
degree zero, so a nonnegative uniform extension slot bound transfers to all
old slots, including the used ones.
-/

namespace WeightedEdgeColoring.RankThreeOptionSystem

open scoped BigOperators

universe u v w u' v' w' x

variable {Job : Type u} {Slot : Type v} {Option : Type w}
  [Fintype Job] [Fintype Slot] [Fintype Option]
  [DecidableEq Job] [DecidableEq Slot] [DecidableEq Option]
  {Job' : Type u'} {Slot' : Type v'} {Option' : Type w'}
  [Fintype Job'] [Fintype Slot'] [Fintype Option']
  [DecidableEq Job'] [DecidableEq Slot'] [DecidableEq Option']
  {Group : Type x} [Fintype Group] [DecidableEq Group]
  {H : RankThreeOptionSystem Job Slot Option}
  {H' : RankThreeOptionSystem Job' Slot' Option'}
  {J S lambda : ℕ}

namespace IsRegularExtension

/-- The copy in the regular extension of a family of distinguished old-job
groups. -/
def liftedOldMembers
    (E : IsRegularExtension H H' J S lambda)
    (members : Group → Finset Job) : Group → Finset Job' :=
  fun g ↦ (members g).map E.jobEmbedding

@[simp] theorem mem_liftedOldMembers_jobEmbedding
    (E : IsRegularExtension H H' J S lambda)
    (members : Group → Finset Job) (g : Group) (j : Job) :
    E.jobEmbedding j ∈ E.liftedOldMembers members g ↔ j ∈ members g := by
  simp [liftedOldMembers]

/-- Lifting old groups creates no new group incidences at an extension job.
This is the row-incidence bound needed by the sharp Harris round. -/
theorem liftedOldMembers_incidence_le
    (E : IsRegularExtension H H' J S lambda)
    (members : Group → Finset Job) (R : ℕ)
    (hincidence : ∀ j,
      ((Finset.univ : Finset Group).filter
        (fun g ↦ j ∈ members g)).card ≤ R) :
    ∀ j',
      ((Finset.univ : Finset Group).filter
        (fun g ↦ j' ∈ E.liftedOldMembers members g)).card ≤ R := by
  intro j'
  by_cases hj' : ∃ j, E.jobEmbedding j = j'
  · rcases hj' with ⟨j, rfl⟩
    simpa using hincidence j
  · have hempty :
        (Finset.univ : Finset Group).filter
            (fun g ↦ j' ∈ E.liftedOldMembers members g) = ∅ := by
      apply Finset.eq_empty_iff_forall_notMem.mpr
      intro g hg
      have hmem := (Finset.mem_filter.mp hg).2
      rcases Finset.mem_map.mp hmem with ⟨j, _hj, hj⟩
      exact hj' ⟨j, hj⟩
    rw [hempty]
    exact Nat.zero_le R

/-- The support of a lifted old-group row consists exactly of the embedded
old options in the original row support. -/
theorem linearRowSupport_liftedOldMembers_eq_map
    (E : IsRegularExtension H H' J S lambda)
    (members : Group → Finset Job) (g : Group) :
    linearRowSupport
        (H'.jobGroupCoverageWeight (E.liftedOldMembers members)) g =
      (linearRowSupport (H.jobGroupCoverageWeight members) g).map
        E.optionEmbedding := by
  rw [H'.linearRowSupport_jobGroupCoverageWeight,
    H.linearRowSupport_jobGroupCoverageWeight]
  ext q
  constructor
  · intro hq
    rcases Finset.mem_biUnion.mp hq with ⟨j', hj'group, hqfiber⟩
    rcases Finset.mem_map.mp hj'group with ⟨j, hjgroup, rfl⟩
    have howner : H'.owner q = E.jobEmbedding j := H'.mem_fiber.mp hqfiber
    rcases E.old_job_induced j q howner with ⟨o, hownerOld, rfl⟩
    apply Finset.mem_map.mpr
    refine ⟨o, Finset.mem_biUnion.mpr ⟨j, hjgroup, ?_⟩, rfl⟩
    exact H.mem_fiber.mpr hownerOld
  · intro hq
    rcases Finset.mem_map.mp hq with ⟨o, ho, rfl⟩
    rcases Finset.mem_biUnion.mp ho with ⟨j, hjgroup, hofiber⟩
    apply Finset.mem_biUnion.mpr
    refine ⟨E.jobEmbedding j,
      Finset.mem_map.mpr ⟨j, hjgroup, rfl⟩, ?_⟩
    apply H'.mem_fiber.mpr
    rw [E.owner_optionEmbedding, H.mem_fiber.mp hofiber]

theorem linearRowSupport_liftedOldMembers_card
    (E : IsRegularExtension H H' J S lambda)
    (members : Group → Finset Job) (g : Group) :
    (linearRowSupport
      (H'.jobGroupCoverageWeight (E.liftedOldMembers members)) g).card =
      (linearRowSupport (H.jobGroupCoverageWeight members) g).card := by
  rw [E.linearRowSupport_liftedOldMembers_eq_map members g, Finset.card_map]

/-- Covered lifted jobs are precisely the images of covered old jobs.  This
uses the induced-on-old-jobs field of a regular extension: a dummy option can
never cover an old job. -/
theorem coveredGroupJobs_liftedOldMembers
    (E : IsRegularExtension H H' J S lambda)
    (members : Group → Finset Job) (g : Group) (M : Finset Option') :
    H'.coveredGroupJobs (E.liftedOldMembers members) g M =
      (H.coveredGroupJobs members g (E.originalSelection M)).map
        E.jobEmbedding := by
  ext j'
  constructor
  · intro hj'
    have hj'parts := Finset.mem_filter.mp hj'
    rcases Finset.mem_map.mp hj'parts.1 with ⟨j, hjgroup, rfl⟩
    apply Finset.mem_map.mpr
    refine ⟨j, Finset.mem_filter.mpr ⟨hjgroup, ?_⟩, rfl⟩
    exact (E.covers_originalSelection_iff M j).mpr hj'parts.2
  · intro hj'
    rcases Finset.mem_map.mp hj' with ⟨j, hjold, rfl⟩
    have hjparts := Finset.mem_filter.mp hjold
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_map.mpr ⟨j, hjparts.1, rfl⟩, ?_⟩
    exact (E.covers_originalSelection_iff M j).mp hjparts.2

/-- For a matching in the extension, its lifted-group row sum is exactly the
old-group row sum of the pulled-back matching. -/
theorem selected_liftedOldMembers_eq_originalSelection
    (E : IsRegularExtension H H' J S lambda)
    (members : Group → Finset Job) (g : Group) (M : Finset Option')
    (hM : H'.IsPartialMatching M) :
    (∑ q ∈ M, H'.jobGroupCoverageWeight
        (E.liftedOldMembers members) g q) =
      ∑ o ∈ E.originalSelection M,
        H.jobGroupCoverageWeight members g o := by
  have hold : H.IsPartialMatching (E.originalSelection M) :=
    E.originalSelection_isPartialMatching M hM
  rw [H'.selected_jobGroupCoverageWeight_eq_coveredGroupJobs
      (E.liftedOldMembers members) g M hM]
  rw [H.selected_jobGroupCoverageWeight_eq_coveredGroupJobs
      members g (E.originalSelection M) hold]
  rw [E.coveredGroupJobs_liftedOldMembers members g M, Finset.card_map]

/-- Project the output of one sharp regular-extension round to the old
system.  The hypothesis `hround` is exactly the qualitative output of
`exists_sharpFixedSlackRound_harris_extra`; keeping it as one argument makes
this bridge independent of the particular numerical way in which the four
Harris inequalities are discharged.

The fourth output line is the exact old-job identity needed for the next
round.  The final line is unconditional in the old slot: if its extension
image was selected, the extension residual degree is zero; otherwise the
slot estimate supplied by `hround` applies. -/
theorem exists_projectedSharpFixedSlackRound
    (E : IsRegularExtension H H' J S lambda)
    (members : Group → Finset Job)
    (groupThreshold : Group → ℝ)
    (jobLower slotUpper : ℝ)
    (hslotUpper0 : 0 ≤ slotUpper)
    (hround : ∃ M : Finset Option',
      H'.IsPartialMatching M ∧
      (∀ g, groupThreshold g <
        ∑ q ∈ M, H'.jobGroupCoverageWeight
          (E.liftedOldMembers members) g q) ∧
      (∀ j', ¬ H'.Covers M j' →
        jobLower ≤ H'.residualJobDegree M j') ∧
      (∀ s', (∀ q ∈ M, s' ∉ H'.slots q) →
        (H'.residualSlotDegree M s' : ℝ) ≤ slotUpper)) :
    ∃ M : Finset Option',
      let A := E.originalSelection M
      let keep := E.originalResidual M
      let Hnext := H.inducedOnOptions keep
      H'.IsPartialMatching M ∧
      H.IsPartialMatching A ∧
      (∀ g, groupThreshold g <
        ∑ o ∈ A, H.jobGroupCoverageWeight members g o) ∧
      (∀ j, (Hnext.fiber j).card =
        H'.residualJobDegree M (E.jobEmbedding j)) ∧
      (∀ j, ¬ H.Covers A j → jobLower ≤ (Hnext.fiber j).card) ∧
      (∀ s, (Hnext.slotDegree s : ℝ) ≤ slotUpper) := by
  rcases hround with ⟨M, hM, hgroup, hjob, hslot⟩
  refine ⟨M, hM, E.originalSelection_isPartialMatching M hM, ?_, ?_, ?_, ?_⟩
  · intro g
    rw [← E.selected_liftedOldMembers_eq_originalSelection members g M hM]
    exact hgroup g
  · intro j
    exact E.induced_originalResidual_fiber_card M j
  · intro j huncovered
    rw [E.induced_originalResidual_fiber_card M j]
    apply hjob (E.jobEmbedding j)
    intro hcovered
    exact huncovered ((E.covers_originalSelection_iff M j).mpr hcovered)
  · intro s
    have hproject := E.induced_originalResidual_slotDegree_le M s
    by_cases hused : ∃ q ∈ M, E.slotEmbedding s ∈ H'.slots q
    · rcases hused with ⟨q, hqM, hqs⟩
      have hzero : H'.residualSlotDegree M (E.slotEmbedding s) = 0 :=
        H'.residualSlotDegree_eq_zero_of_selected_uses M
          (E.slotEmbedding s) hqM hqs
      have holdzero :
          (H.inducedOnOptions (E.originalResidual M)).slotDegree s = 0 := by
        omega
      rw [holdzero]
      simpa using hslotUpper0
    · have hunused : ∀ q ∈ M, E.slotEmbedding s ∉ H'.slots q := by
        intro q hqM hqs
        exact hused ⟨q, hqM, hqs⟩
      have hext := hslot (E.slotEmbedding s) hunused
      have hprojectR :
          ((H.inducedOnOptions (E.originalResidual M)).slotDegree s : ℝ) ≤
            (H'.residualSlotDegree M (E.slotEmbedding s) : ℝ) := by
        exact_mod_cast hproject
      exact hprojectR.trans hext

/-- The fixed-slack specialization of the preceding projection theorem.
This is the recurrence consumed by iteration after a regularization step.
All probabilistic and local-lemma work remains confined to the extension
round hypothesis. -/
theorem exists_projectedSharpFixedSlackRound_fixedSlack
    (E : IsRegularExtension H H' J S lambda)
    (members : Group → Finset Job)
    (groupThreshold : Group → ℝ)
    (d : ℕ) (a gamma etaJob etaLoad etaCollision : ℝ)
    (hgamma1 : gamma ≤ 1)
    (herror : (1 - gamma) * etaJob + etaLoad + etaCollision ≤
      a * gamma * (1 - gamma))
    (hslotUpper0 :
      0 ≤ (WeightedEdgeColoring.fixedSlackSlotRetention a gamma * (1 - gamma) +
        etaLoad + etaCollision) * d)
    (hround : ∃ M : Finset Option',
      H'.IsPartialMatching M ∧
      (∀ g, groupThreshold g <
        ∑ q ∈ M, H'.jobGroupCoverageWeight
          (E.liftedOldMembers members) g q) ∧
      (∀ j', ¬ H'.Covers M j' →
        (WeightedEdgeColoring.fixedSlackJobRetention a gamma - etaJob) * d ≤
          H'.residualJobDegree M j') ∧
      (∀ s', (∀ q ∈ M, s' ∉ H'.slots q) →
        (H'.residualSlotDegree M s' : ℝ) ≤
          (WeightedEdgeColoring.fixedSlackSlotRetention a gamma * (1 - gamma) +
            etaLoad + etaCollision) * d)) :
    ∃ M : Finset Option',
      let A := E.originalSelection M
      let keep := E.originalResidual M
      let Hnext := H.inducedOnOptions keep
      H'.IsPartialMatching M ∧
      H.IsPartialMatching A ∧
      (∀ g, groupThreshold g <
        ∑ o ∈ A, H.jobGroupCoverageWeight members g o) ∧
      (∀ j, (Hnext.fiber j).card =
        H'.residualJobDegree M (E.jobEmbedding j)) ∧
      (∀ j, ¬ H.Covers A j →
        (WeightedEdgeColoring.fixedSlackJobRetention a gamma - etaJob) * d ≤
          (Hnext.fiber j).card) ∧
      (∀ s, (Hnext.slotDegree s : ℝ) ≤
        (WeightedEdgeColoring.fixedSlackSlotRetention a gamma * (1 - gamma) +
          etaLoad + etaCollision) * d) ∧
      (∀ j s, ¬ H.Covers A j →
        (Hnext.slotDegree s : ℝ) ≤
          (1 - gamma) * (Hnext.fiber j).card) := by
  rcases E.exists_projectedSharpFixedSlackRound members groupThreshold
      ((WeightedEdgeColoring.fixedSlackJobRetention a gamma - etaJob) * d)
      ((WeightedEdgeColoring.fixedSlackSlotRetention a gamma * (1 - gamma) +
        etaLoad + etaCollision) * d) hslotUpper0 hround with
    ⟨M, hExtensionMatching, hmatching, hgroup, hexact, hjob, hslot⟩
  refine ⟨M, hExtensionMatching, hmatching, hgroup, hexact, hjob, hslot, ?_⟩
  intro j s huncovered
  exact sharpFixedSlack_output_preserves_same_gap d a gamma etaJob etaLoad
    etaCollision ((H.inducedOnOptions (E.originalResidual M)).fiber j).card
    ((H.inducedOnOptions (E.originalResidual M)).slotDegree s)
    hgamma1 herror (hjob j huncovered) (hslot s)

end IsRegularExtension

end WeightedEdgeColoring.RankThreeOptionSystem
