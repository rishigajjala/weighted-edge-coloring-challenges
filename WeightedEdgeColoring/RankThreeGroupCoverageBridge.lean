import WeightedEdgeColoring.RankThreeResidualHarrisBridge

/-!
# Deterministic bridge from group rows to covered jobs

Job fibres are disjoint because every option has one owner. Consequently a
job-group row has support equal to the sum of the fibre sizes. For a partial
matching, the selected row sum counts covered jobs in the group exactly.
-/

namespace WeightedEdgeColoring.RankThreeOptionSystem

open scoped BigOperators

universe u v w x

variable {Job : Type u} {Slot : Type v} {Option : Type w} {Group : Type x}
  [Fintype Job] [Fintype Slot] [Fintype Option] [Fintype Group]
  [DecidableEq Job] [DecidableEq Slot] [DecidableEq Option] [DecidableEq Group]
  (H : RankThreeOptionSystem Job Slot Option)

theorem fiber_disjoint_of_ne {j k : Job} (hjk : j ≠ k) :
    Disjoint (H.fiber j) (H.fiber k) := by
  rw [Finset.disjoint_left]
  intro o hoj hok
  exact hjk ((H.mem_fiber.mp hoj).symm.trans (H.mem_fiber.mp hok))

/-- Exact support size of a job-group coverage row. -/
theorem jobGroupCoverage_support_card_eq_sum
    (members : Group → Finset Job) (g : Group) :
    (linearRowSupport (H.jobGroupCoverageWeight members) g).card =
      ∑ j ∈ members g, (H.fiber j).card := by
  rw [H.linearRowSupport_jobGroupCoverageWeight members g]
  apply Finset.card_biUnion
  intro j hj k hk hjk
  exact H.fiber_disjoint_of_ne hjk

/-- A group of at least `k` jobs, each with at least `d` options, has support
at least `k*d`. -/
theorem jobGroupCoverage_support_card_ge
    (members : Group → Finset Job) (g : Group) (k d : ℕ)
    (hgroup : k ≤ (members g).card)
    (hdegree : ∀ j ∈ members g, d ≤ (H.fiber j).card) :
    k * d ≤ (linearRowSupport (H.jobGroupCoverageWeight members) g).card := by
  rw [H.jobGroupCoverage_support_card_eq_sum members g]
  calc
    k * d ≤ (members g).card * d := Nat.mul_le_mul_right d hgroup
    _ = ∑ _j ∈ members g, d := by simp
    _ ≤ ∑ j ∈ members g, (H.fiber j).card :=
      Finset.sum_le_sum fun j hj ↦ hdegree j hj

/-- Jobs from `members g` covered by `S`. -/
def coveredGroupJobs (members : Group → Finset Job)
    (g : Group) (S : Finset Option) : Finset Job :=
  (members g).filter fun j ↦ H.Covers S j

/-- A job is in `coveredGroupJobs` exactly when it belongs to the group and
is the owner of a selected option. -/
theorem mem_coveredGroupJobs_iff
    (members : Group → Finset Job) (g : Group) (S : Finset Option) (j : Job) :
    j ∈ H.coveredGroupJobs members g S ↔
      j ∈ members g ∧ ∃ o ∈ S, H.owner o = j := by
  simp [coveredGroupJobs, Covers]

/-- The raw selected group-row sum is the number of selected options whose
owner lies in the group. -/
theorem selected_jobGroupCoverageWeight_eq_card
    (members : Group → Finset Job) (g : Group) (S : Finset Option) :
    (∑ o ∈ S, H.jobGroupCoverageWeight members g o) =
      ((S.filter fun o ↦ H.owner o ∈ members g).card : ℝ) := by
  simp [jobGroupCoverageWeight]

/-- In a partial matching, the raw selected group-row sum counts covered
jobs in the group exactly. -/
theorem selected_jobGroupCoverageWeight_eq_coveredGroupJobs
    (members : Group → Finset Job) (g : Group) (S : Finset Option)
    (hS : H.IsPartialMatching S) :
    (∑ o ∈ S, H.jobGroupCoverageWeight members g o) =
      ((H.coveredGroupJobs members g S).card : ℝ) := by
  rw [H.selected_jobGroupCoverageWeight_eq_card members g S]
  apply congrArg Nat.cast
  let selected : Finset Option := S.filter fun o ↦ H.owner o ∈ members g
  have hinj : Set.InjOn H.owner (selected : Set Option) := by
    intro o ho p hp hopen
    exact hS.2 (Finset.mem_filter.mp ho).1 (Finset.mem_filter.mp hp).1 hopen
  have hcard : (selected.image H.owner).card = selected.card :=
    Finset.card_image_iff.mpr (by
      intro o ho p hp hopen
      exact hinj ho hp hopen)
  have himage : selected.image H.owner = H.coveredGroupJobs members g S := by
    ext j
    simp only [Finset.mem_image, Finset.mem_filter, selected, coveredGroupJobs,
      Covers]
    constructor
    · rintro ⟨o, ⟨hoS, hogroup⟩, howner⟩
      exact ⟨howner ▸ hogroup, o, hoS, howner⟩
    · rintro ⟨hjgroup, o, hoS, howner⟩
      exact ⟨o, ⟨hoS, howner.symm ▸ hjgroup⟩, howner⟩
  rw [← himage, hcard]

/-- Any strict lower bound on the selected row sum gives the same strict
lower bound on the number of covered jobs in the group. -/
theorem coveredGroupJobs_count_gt_of_row_gt
    (members : Group → Finset Job) (g : Group) (S : Finset Option)
    (hS : H.IsPartialMatching S) (threshold : ℝ)
    (hrow : threshold <
      ∑ o ∈ S, H.jobGroupCoverageWeight members g o) :
    threshold < (H.coveredGroupJobs members g S).card := by
  rw [H.selected_jobGroupCoverageWeight_eq_coveredGroupJobs members g S hS] at hrow
  exact hrow

end WeightedEdgeColoring.RankThreeOptionSystem
