import WeightedEdgeColoring.RankThreePairCounting

namespace WeightedEdgeColoring

universe u v w

namespace RankThreeOptionSystem

variable {Job : Type u} {Slot : Type v} {Option : Type w}
  [Fintype Job] [Fintype Slot] [Fintype Option]
  [DecidableEq Job] [DecidableEq Slot] [DecidableEq Option]
  (H : RankThreeOptionSystem Job Slot Option)

/-!
# One augmenting-frontier growth step

The arbitrary-depth exchange obstruction supplies a frontier job with few
options compatible with the untouched matching.  If every job fibre is
large, the missing options must be blocked by many distinct options of the
untouched matching.  This file records that counting step and its natural
division form.
-/

/-- Selected options in `M` that block at least one option of job `j`. -/
def blockersOf (j : Job) (M : Finset Option) : Finset Option :=
  M.filter fun p ↦ (H.blockedBy j p).Nonempty

@[simp] theorem mem_blockersOf {j : Job} {M : Finset Option} {p : Option} :
    p ∈ H.blockersOf j M ↔
      p ∈ M ∧ (H.blockedBy j p).Nonempty := by
  simp [blockersOf]

/-- Removing blockers that block no option does not change the union of
blocked options. -/
theorem blockedBySet_eq_blockers_biUnion (j : Job) (M : Finset Option) :
    H.blockedBySet j M =
      (H.blockersOf j M).biUnion (H.blockedBy j) := by
  ext q
  constructor
  · intro hq
    obtain ⟨p, hpM, hqp⟩ := Finset.mem_biUnion.mp hq
    apply Finset.mem_biUnion.mpr
    exact ⟨p, H.mem_blockersOf.mpr ⟨hpM, ⟨q, hqp⟩⟩, hqp⟩
  · intro hq
    obtain ⟨p, hp, hqp⟩ := Finset.mem_biUnion.mp hq
    apply Finset.mem_biUnion.mpr
    exact ⟨p, (H.mem_blockersOf.mp hp).1, hqp⟩

/-- Count a blocked union using only the selected options that actually
block something. -/
theorem card_blockedBySet_le_blockers_mul
    (j : Job) (M : Finset Option) (r : ℕ)
    (hblock : ∀ p ∈ H.blockersOf j M,
      (H.blockedBy j p).card ≤ r) :
    (H.blockedBySet j M).card ≤ (H.blockersOf j M).card * r := by
  rw [H.blockedBySet_eq_blockers_biUnion j M]
  calc
    ((H.blockersOf j M).biUnion (H.blockedBy j)).card ≤
        ∑ p ∈ H.blockersOf j M, (H.blockedBy j p).card :=
      Finset.card_biUnion_le
    _ ≤ ∑ _p ∈ H.blockersOf j M, r := by
      exact Finset.sum_le_sum hblock
    _ = (H.blockersOf j M).card * r := by simp

/-- Under a job-slot codegree bound, each actual blocker accounts for at
most `2 * lambda` blocked options. -/
theorem card_blockedBySet_le_two_mul_blockers
    (j : Job) (M : Finset Option) (lambda : ℕ)
    (hcodeg : ∀ s : Slot, H.jobSlotCodegree j s ≤ lambda) :
    (H.blockedBySet j M).card ≤
      (H.blockersOf j M).card * (2 * lambda) := by
  apply H.card_blockedBySet_le_blockers_mul j M (2 * lambda)
  intro p _hp
  apply H.card_blockedBy_le_two_mul j p lambda
  intro s _hs
  exact hcodeg s

/-- Every job in the root-plus-deleted-owner frontier is absent from the
untouched matching `M \ P`. -/
theorem frontier_not_covered_by_sdiff
    {M P : Finset Option} (hM : H.IsPartialMatching M)
    (hP : P ⊆ M) (root : Job) (hroot : ¬ H.Covers M root)
    {j : Job} (hj : j ∈ insert root (P.image H.owner)) :
    ¬ H.Covers (M \ P) j := by
  intro hcover
  obtain ⟨q, hqrest, hqowner⟩ := hcover
  have hqdata := Finset.mem_sdiff.mp hqrest
  rcases Finset.mem_insert.mp hj with rfl | hjP
  · exact hroot ⟨q, hqdata.1, hqowner⟩
  · obtain ⟨p, hpP, hpowner⟩ := Finset.mem_image.mp hjP
    have hqp : q = p :=
      hM.2 hqdata.1 (hP hpP) (hqowner.trans hpowner.symm)
    exact hqdata.2 (hqp ▸ hpP)

/-- Existential form of the all-frontier-density obstruction.  Some
frontier job has at most `P.card * (2 * lambda)` locally eligible options. -/
theorem exists_frontier_job_with_small_exchangePool
    {M P : Finset Option}
    (hM : H.IsPartialMatching M)
    (hmaxM : ∀ M' : Finset Option,
      H.IsPartialMatching M' → M'.card ≤ M.card)
    (hP : P ⊆ M) (root : Job) (hroot : ¬ H.Covers M root)
    (lambda : ℕ)
    (hcodeg : ∀ j : Job, ∀ s : Slot,
      H.jobSlotCodegree j s ≤ lambda) :
    ∃ j ∈ insert root (P.image H.owner),
      (H.fiber j ∩ H.exchangePool M P).card ≤
        P.card * (2 * lambda) := by
  have hnot := H.maximum_partialMatching_not_all_frontier_dense
    hM hmaxM hP root hroot lambda hcodeg
  push Not at hnot
  exact hnot

/-- One quantitative frontier-growth step.  If every job has at least `m`
options, then some frontier job has enough missing mass to force many
distinct blockers in the untouched matching:

`m - |P| * (2*lambda) ≤ blockerCount * (2*lambda)`.
-/
theorem exists_frontier_job_blocker_lower_bound
    {M P : Finset Option}
    (hM : H.IsPartialMatching M)
    (hmaxM : ∀ M' : Finset Option,
      H.IsPartialMatching M' → M'.card ≤ M.card)
    (hP : P ⊆ M) (root : Job) (hroot : ¬ H.Covers M root)
    (m lambda : ℕ)
    (hdegree : ∀ j : Job, m ≤ (H.fiber j).card)
    (hcodeg : ∀ j : Job, ∀ s : Slot,
      H.jobSlotCodegree j s ≤ lambda) :
    ∃ j ∈ insert root (P.image H.owner),
      m - P.card * (2 * lambda) ≤
        (H.blockersOf j (M \ P)).card * (2 * lambda) := by
  obtain ⟨j, hj, heligible⟩ :=
    H.exists_frontier_job_with_small_exchangePool
      hM hmaxM hP root hroot lambda hcodeg
  have huncovered : ¬ H.Covers (M \ P) j :=
    H.frontier_not_covered_by_sdiff hM hP root hroot hj
  have hsplit := H.card_fiber_inter_exchangePool_add_blocked j huncovered
  have hblockedLower : m - P.card * (2 * lambda) ≤
      (H.blockedBySet j (M \ P)).card := by
    have hdeg := hdegree j
    omega
  have hblockedUpper : (H.blockedBySet j (M \ P)).card ≤
      (H.blockersOf j (M \ P)).card * (2 * lambda) :=
    H.card_blockedBySet_le_two_mul_blockers
      j (M \ P) lambda (hcodeg j)
  exact ⟨j, hj, hblockedLower.trans hblockedUpper⟩

/-- Symmetric multiplication-order version of the blocker lower bound. -/
theorem exists_frontier_job_blocker_lower_bound_left
    {M P : Finset Option}
    (hM : H.IsPartialMatching M)
    (hmaxM : ∀ M' : Finset Option,
      H.IsPartialMatching M' → M'.card ≤ M.card)
    (hP : P ⊆ M) (root : Job) (hroot : ¬ H.Covers M root)
    (m lambda : ℕ)
    (hdegree : ∀ j : Job, m ≤ (H.fiber j).card)
    (hcodeg : ∀ j : Job, ∀ s : Slot,
      H.jobSlotCodegree j s ≤ lambda) :
    ∃ j ∈ insert root (P.image H.owner),
      m - (2 * lambda) * P.card ≤
        (2 * lambda) * (H.blockersOf j (M \ P)).card := by
  simpa [Nat.mul_comm] using
    H.exists_frontier_job_blocker_lower_bound
      hM hmaxM hP root hroot m lambda hdegree hcodeg

/-- Division form: some frontier job has at least the displayed quotient
many distinct blockers in `M \ P`.  No positivity assumption is needed for
`Nat.div_le_of_le_mul`; when `lambda = 0`, the preceding inequality already
forces the numerator to vanish. -/
theorem exists_frontier_job_blocker_div_lower_bound
    {M P : Finset Option}
    (hM : H.IsPartialMatching M)
    (hmaxM : ∀ M' : Finset Option,
      H.IsPartialMatching M' → M'.card ≤ M.card)
    (hP : P ⊆ M) (root : Job) (hroot : ¬ H.Covers M root)
    (m lambda : ℕ)
    (hdegree : ∀ j : Job, m ≤ (H.fiber j).card)
    (hcodeg : ∀ j : Job, ∀ s : Slot,
      H.jobSlotCodegree j s ≤ lambda) :
    ∃ j ∈ insert root (P.image H.owner),
      (m - (2 * lambda) * P.card) / (2 * lambda) ≤
        (H.blockersOf j (M \ P)).card := by
  obtain ⟨j, hj, hbound⟩ :=
    H.exists_frontier_job_blocker_lower_bound_left
      hM hmaxM hP root hroot m lambda hdegree hcodeg
  refine ⟨j, hj, Nat.div_le_of_le_mul ?_⟩
  simpa [Nat.mul_comm] using hbound

end RankThreeOptionSystem

end WeightedEdgeColoring
