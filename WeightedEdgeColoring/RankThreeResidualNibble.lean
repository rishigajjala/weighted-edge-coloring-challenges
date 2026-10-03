import WeightedEdgeColoring.RankThreeIsolatedNibble

/-!
# Residual systems and weighted one-round nibble coverage

This file develops the bookkeeping needed to iterate isolated-nibble rounds.
It also strengthens the one-round cardinality estimate to arbitrary
nonnegative weights on jobs.  The weighted theorem is useful for measuring
coverage inside one prescribed original star, but does not claim simultaneous
near-coverage for every star.
-/

namespace WeightedEdgeColoring.RankThreeOptionSystem

open scoped BigOperators
open WeightedEdgeColoring.FiniteBernoulliChernoff

universe u v w

variable {Job : Type u} {Slot : Type v} {Option : Type w}
  [Fintype Job] [Fintype Slot] [Fintype Option]
  [DecidableEq Job] [DecidableEq Slot] [DecidableEq Option]
  (H : RankThreeOptionSystem Job Slot Option)

/-- Options still available after a partial matching: their owner is new and
they are slot-compatible with every previously selected option. -/
def residualOptions (M : Finset Option) : Finset Option :=
  Finset.univ.filter fun o ↦ ∀ p ∈ M,
    H.owner o ≠ H.owner p ∧ H.Compatible o p

@[simp] theorem mem_residualOptions {M : Finset Option} {o : Option} :
    o ∈ H.residualOptions M ↔ ∀ p ∈ M,
      H.owner o ≠ H.owner p ∧ H.Compatible o p := by
  simp [residualOptions]

/-- Available options of one job in the residual system. -/
def residualFiber (M : Finset Option) (j : Job) : Finset Option :=
  (H.residualOptions M).filter fun o ↦ H.owner o = j

@[simp] theorem mem_residualFiber {M : Finset Option} {j : Job} {o : Option} :
    o ∈ H.residualFiber M j ↔
      H.owner o = j ∧ ∀ p ∈ M,
        H.owner o ≠ H.owner p ∧ H.Compatible o p := by
  simp [residualFiber, and_comm]

/-- Residual degree of one job. -/
def residualJobDegree (M : Finset Option) (j : Job) : ℕ :=
  (H.residualFiber M j).card

/-- Residual degree of one slot. -/
def residualSlotDegree (M : Finset Option) (s : Slot) : ℕ :=
  ((H.residualOptions M).filter fun o ↦ s ∈ H.slots o).card

/-- The option type of the residual system. -/
abbrev ResidualOption (M : Finset Option) :=
  {o : Option // o ∈ H.residualOptions M}

/-- The residual options, with the original owners and slots, form another
rank-three option system.  This is the object on which a later nibble round
is run. -/
def residualSystem (M : Finset Option) :
    RankThreeOptionSystem Job Slot (H.ResidualOption M) where
  owner o := H.owner o.1
  slots o := H.slots o.1
  slots_card_le_two o := H.slots_card_le_two o.1

/-- The fibre size in the residual option system is the residual job degree
defined on the original option type. -/
theorem residualSystem_fiber_card (M : Finset Option) (j : Job) :
    ((H.residualSystem M).fiber j).card = H.residualJobDegree M j := by
  let valEmbedding : H.ResidualOption M ↪ Option :=
    ⟨fun o ↦ o.1, Subtype.val_injective⟩
  have hmap : ((H.residualSystem M).fiber j).map valEmbedding =
      H.residualFiber M j := by
    ext o
    simp [valEmbedding, residualSystem, residualFiber, and_comm]
  have hcard := congrArg Finset.card hmap
  change ((H.residualSystem M).fiber j).card =
    (H.residualFiber M j).card
  simpa using hcard

/-- Likewise, residual-system slot degree agrees with the original-type
residual slot degree. -/
theorem residualSystem_slotDegree_card (M : Finset Option) (s : Slot) :
    ((Finset.univ : Finset (H.ResidualOption M)).filter
      fun o ↦ s ∈ (H.residualSystem M).slots o).card =
      H.residualSlotDegree M s := by
  let valEmbedding : H.ResidualOption M ↪ Option :=
    ⟨fun o ↦ o.1, Subtype.val_injective⟩
  have hmap : (((Finset.univ : Finset (H.ResidualOption M)).filter
      fun o ↦ s ∈ (H.residualSystem M).slots o).map valEmbedding) =
      (H.residualOptions M).filter fun o ↦ s ∈ H.slots o := by
    ext o
    simp [valEmbedding, residualSystem, and_comm]
  have hcard := congrArg Finset.card hmap
  simpa [residualSlotDegree] using hcard

/-- Adding selected options intersects the two residual option sets exactly. -/
theorem residualOptions_union (M A : Finset Option) :
    H.residualOptions (M ∪ A) =
      H.residualOptions M ∩ H.residualOptions A := by
  ext o
  simp only [mem_residualOptions, Finset.mem_inter, Finset.mem_union]
  constructor
  · intro h
    constructor
    · intro p hp
      exact h p (Or.inl hp)
    · intro p hp
      exact h p (Or.inr hp)
  · rintro ⟨hM, hA⟩ p (hp | hp)
    · exact hM p hp
    · exact hA p hp

theorem residualOptions_anti {M A : Finset Option} (hMA : M ⊆ A) :
    H.residualOptions A ⊆ H.residualOptions M := by
  intro o ho
  rw [H.mem_residualOptions] at ho ⊢
  intro p hp
  exact ho p (hMA hp)

theorem residualFiber_anti {M A : Finset Option} (hMA : M ⊆ A) (j : Job) :
    H.residualFiber A j ⊆ H.residualFiber M j := by
  intro o ho
  have hmem := H.mem_residualFiber.mp ho
  exact H.mem_residualFiber.mpr ⟨hmem.1,
    fun p hp ↦ hmem.2 p (hMA hp)⟩

/-- Options of `j` deleted in the update from residual set `M` to `M ∪ A`. -/
def removedResidualFiber (M A : Finset Option) (j : Job) : Finset Option :=
  H.residualFiber M j \ H.residualFiber (M ∪ A) j

/-- Exact one-round job-degree update. -/
theorem residualJobDegree_union_add_removed
    (M A : Finset Option) (j : Job) :
    H.residualJobDegree (M ∪ A) j +
        (H.removedResidualFiber M A j).card =
      H.residualJobDegree M j := by
  unfold residualJobDegree removedResidualFiber
  simpa [add_comm] using Finset.card_sdiff_add_card_eq_card
    (H.residualFiber_anti (Finset.subset_union_left) j)

/-- Options using `s` that are deleted in one residual update. -/
def removedResidualSlot (M A : Finset Option) (s : Slot) : Finset Option :=
  ((H.residualOptions M).filter fun o ↦ s ∈ H.slots o) \
    ((H.residualOptions (M ∪ A)).filter fun o ↦ s ∈ H.slots o)

/-- Exact one-round slot-degree update. -/
theorem residualSlotDegree_union_add_removed
    (M A : Finset Option) (s : Slot) :
    H.residualSlotDegree (M ∪ A) s +
        (H.removedResidualSlot M A s).card =
      H.residualSlotDegree M s := by
  unfold residualSlotDegree removedResidualSlot
  simpa [add_comm] using Finset.card_sdiff_add_card_eq_card (by
    intro o ho
    exact Finset.mem_filter.mpr
      ⟨H.residualOptions_anti Finset.subset_union_left
        (Finset.mem_filter.mp ho).1, (Finset.mem_filter.mp ho).2⟩)

/-- The weight of jobs represented by a partial matching. -/
def coveredJobWeight (jobWeight : Job → ℝ) (M : Finset Option) : ℝ :=
  ∑ o ∈ M, jobWeight (H.owner o)

/-- Exact expectation decomposition for weighted isolated coverage. -/
theorem expected_isolated_coveredJobWeight
    (q : Option → ℝ) (jobWeight : Job → ℝ) :
    (∑ S : Finset Option, bernoulliMass q S *
      H.coveredJobWeight jobWeight (H.isolatedOptions S)) =
      ∑ o : Option, jobWeight (H.owner o) *
        (∑ S : Finset Option, bernoulliMass q S *
          (if o ∈ H.isolatedOptions S then (1 : ℝ) else 0)) := by
  have hweight (S : Finset Option) :
      H.coveredJobWeight jobWeight (H.isolatedOptions S) =
        ∑ o : Option,
          jobWeight (H.owner o) *
            (if o ∈ H.isolatedOptions S then (1 : ℝ) else 0) := by
    unfold coveredJobWeight
    symm
    calc
      (∑ o : Option, jobWeight (H.owner o) *
          (if o ∈ H.isolatedOptions S then (1 : ℝ) else 0)) =
          ∑ o : Option,
            if o ∈ H.isolatedOptions S then jobWeight (H.owner o) else 0 := by
        apply Finset.sum_congr rfl
        intro o _ho
        by_cases hmem : o ∈ H.isolatedOptions S <;> simp [hmem]
      _ = ∑ o ∈ H.isolatedOptions S, jobWeight (H.owner o) := by
        rw [← Finset.sum_filter]
        apply Finset.sum_congr
        · ext o
          simp
        · intro o _ho
          rfl
  simp_rw [hweight, Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro o _ho
  apply Finset.sum_congr rfl
  intro S _hS
  ring

/-- A one-round isolated nibble captures the corresponding fraction of every
nonnegative weighted sum of jobs, in expectation. -/
theorem expected_isolated_coveredJobWeight_lower
    (q : Option → ℝ) (jobWeight : Job → ℝ)
    (hq0 : ∀ o, 0 ≤ q o) (hq1 : ∀ o, q o ≤ 1)
    (hweight0 : ∀ j, 0 ≤ jobWeight j)
    (delta : ℝ) (hdelta : ∀ o, H.conflictLoad q o ≤ delta) :
    (1 - delta) *
        (∑ o : Option, q o * jobWeight (H.owner o)) ≤
      ∑ S : Finset Option, bernoulliMass q S *
        H.coveredJobWeight jobWeight (H.isolatedOptions S) := by
  rw [H.expected_isolated_coveredJobWeight q jobWeight, Finset.mul_sum]
  apply Finset.sum_le_sum
  intro o _ho
  have hsurvive := H.expected_isolated_indicator_lower q hq0 hq1 o
  have hbase : (1 - delta) * q o ≤
      q o * (1 - H.conflictLoad q o) := by
    rw [mul_comm (1 - delta)]
    exact mul_le_mul_of_nonneg_left
      (sub_le_sub_left (hdelta o) 1) (hq0 o)
  calc
    (1 - delta) * (q o * jobWeight (H.owner o)) =
        jobWeight (H.owner o) * ((1 - delta) * q o) := by ring
    _ ≤ jobWeight (H.owner o) *
        (q o * (1 - H.conflictLoad q o)) :=
      mul_le_mul_of_nonneg_left hbase (hweight0 (H.owner o))
    _ ≤ jobWeight (H.owner o) *
        (∑ S : Finset Option, bernoulliMass q S *
          (if o ∈ H.isolatedOptions S then (1 : ℝ) else 0)) :=
      mul_le_mul_of_nonneg_left hsurvive (hweight0 (H.owner o))

/-- Some one-round outcome attains the weighted expectation. -/
theorem exists_isolated_coveredJobWeight_ge_expectation
    (q : Option → ℝ) (jobWeight : Job → ℝ)
    (hq0 : ∀ o, 0 ≤ q o) (hq1 : ∀ o, q o ≤ 1) :
    ∃ S : Finset Option,
      (∑ T : Finset Option, bernoulliMass q T *
        H.coveredJobWeight jobWeight (H.isolatedOptions T)) ≤
      H.coveredJobWeight jobWeight (H.isolatedOptions S) := by
  classical
  obtain ⟨S, _hS, hmax⟩ :=
    Finset.exists_max_image (Finset.univ : Finset (Finset Option))
      (fun T ↦ H.coveredJobWeight jobWeight (H.isolatedOptions T))
      ⟨∅, Finset.mem_univ ∅⟩
  refine ⟨S, ?_⟩
  calc
    (∑ T : Finset Option, bernoulliMass q T *
        H.coveredJobWeight jobWeight (H.isolatedOptions T)) ≤
      ∑ T : Finset Option, bernoulliMass q T *
        H.coveredJobWeight jobWeight (H.isolatedOptions S) := by
      apply Finset.sum_le_sum
      intro T _hT
      exact mul_le_mul_of_nonneg_left
        (hmax T (Finset.mem_univ T))
        (bernoulliMass_nonneg q hq0 hq1 T)
    _ = H.coveredJobWeight jobWeight (H.isolatedOptions S) := by
      rw [← Finset.sum_mul, sum_bernoulliMass, one_mul]

/-- A deterministic one-round partial matching with the weighted coverage
guaranteed by the isolated-nibble survival estimate. -/
theorem exists_isolated_partialMatching_of_weighted_coverage
    (q : Option → ℝ) (jobWeight : Job → ℝ)
    (hq0 : ∀ o, 0 ≤ q o) (hq1 : ∀ o, q o ≤ 1)
    (hweight0 : ∀ j, 0 ≤ jobWeight j)
    (delta : ℝ) (hdelta : ∀ o, H.conflictLoad q o ≤ delta) :
    ∃ M : Finset Option,
      H.IsPartialMatching M ∧
      (1 - delta) *
          (∑ o : Option, q o * jobWeight (H.owner o)) ≤
        H.coveredJobWeight jobWeight M := by
  rcases H.exists_isolated_coveredJobWeight_ge_expectation
    q jobWeight hq0 hq1 with ⟨S, hS⟩
  refine ⟨H.isolatedOptions S, H.isolatedOptions_isPartialMatching S, ?_⟩
  exact (H.expected_isolated_coveredJobWeight_lower q jobWeight
    hq0 hq1 hweight0 delta hdelta).trans hS

end WeightedEdgeColoring.RankThreeOptionSystem
