import WeightedEdgeColoring.RankThreeGroupCoverageBridge

/-!
# Jobs with a nonempty current option fibre

Residual systems retain the original finite job type, including jobs already
covered in earlier rounds.  The useful active set consists exactly of jobs
whose current fibre is nonempty.  Owner-local degree bounds automatically
become uniform lower bounds on this active set.
-/

namespace WeightedEdgeColoring.RankThreeOptionSystem

universe u v w

variable {Job : Type u} {Slot : Type v} {Option : Type w}
  [Fintype Job] [Fintype Slot] [Fintype Option]
  [DecidableEq Job] [DecidableEq Slot] [DecidableEq Option]
  (H : RankThreeOptionSystem Job Slot Option)

/-- Jobs that still own at least one available option. -/
def activeJobs : Finset Job :=
  Finset.univ.filter fun j ↦ (H.fiber j).Nonempty

@[simp] theorem mem_activeJobs (j : Job) :
    j ∈ H.activeJobs ↔ (H.fiber j).Nonempty := by
  simp [activeJobs]

/-- The owner of every option is active. -/
theorem owner_mem_activeJobs (o : Option) : H.owner o ∈ H.activeJobs := by
  rw [H.mem_activeJobs]
  exact ⟨o, H.mem_fiber.mpr rfl⟩

/-- An owner-local lower bound is uniform over all active job fibres. -/
theorem fiber_card_ge_of_mem_activeJobs
    (d : ℕ) (hlower : ∀ o, d ≤ (H.fiber (H.owner o)).card)
    {j : Job} (hj : j ∈ H.activeJobs) :
    d ≤ (H.fiber j).card := by
  rcases (H.mem_activeJobs j).mp hj with ⟨o, ho⟩
  have howner : H.owner o = j := H.mem_fiber.mp ho
  simpa [howner] using hlower o

/-- A group contained in the active set inherits the usual product lower
bound on its coverage-row support from an owner-local degree invariant. -/
theorem jobGroupCoverage_support_card_ge_of_active
    {Group : Type*} [Fintype Group] [DecidableEq Group]
    (members : Group → Finset Job) (g : Group) (k d : ℕ)
    (hlower : ∀ o, d ≤ (H.fiber (H.owner o)).card)
    (hgroup : k ≤ (members g).card)
    (hactive : members g ⊆ H.activeJobs) :
    k * d ≤
      (linearRowSupport (H.jobGroupCoverageWeight members) g).card := by
  apply H.jobGroupCoverage_support_card_ge members g k d hgroup
  intro j hj
  exact H.fiber_card_ge_of_mem_activeJobs d hlower (hactive hj)

end WeightedEdgeColoring.RankThreeOptionSystem
