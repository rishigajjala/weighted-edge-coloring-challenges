import WeightedEdgeColoring.RankThreeResidualTwoSidedHarris
import WeightedEdgeColoring.RankThreeResidualUniformLowerMean
import WeightedEdgeColoring.RankThreeResidualDegreeMean
import WeightedEdgeColoring.RankThreeResidualHarrisExponential

/-!
# A uniform two-sided round for active slot rows

For iteration, lower deletion is needed only at slots whose current degree is
still large.  Low-degree slots must be omitted from the lower-tail family.
Upper deletion is needed only on job rows, in order to keep every surviving
job fibre large.

This file therefore uses lower rows

`Group ⊕ {s : Slot // dSlot ≤ slotDegree s}`

and job rows as the upper-tail family.  It first discharges the structural
rank-three incidence conditions and then gives a uniform exponential-product
specialization.  This is a one-round theorem; no persistence or iteration is
claimed here.
-/

namespace WeightedEdgeColoring.RankThreeOptionSystem

open scoped BigOperators
open WeightedEdgeColoring.FiniteBernoulliSupportSplit

universe u v w x

variable {Job : Type u} {Slot : Type v} {Option : Type w} {Group : Type x}
  [Fintype Job] [Fintype Slot] [Fintype Option] [Fintype Group]
  [DecidableEq Job] [DecidableEq Slot] [DecidableEq Option] [DecidableEq Group]
  (H : RankThreeOptionSystem Job Slot Option)

/-- Slots whose current degree is at least the declared active scale. -/
abbrev ActiveSlot (dSlot : ℕ) := {s : Slot // dSlot ≤ H.slotDegree s}

/-- Group rows together with lower deletion rows for active slots. -/
abbrev ActiveSlotLowerRow (dSlot : ℕ) := Group ⊕ H.ActiveSlot dSlot

/-- The lower-row coefficients: group coverage on the left and normalized
slot deletion on the right. -/
noncomputable def activeSlotLowerWeight
    (members : Group → Finset Job) (lambda dSlot : ℕ) :
    H.ActiveSlotLowerRow (Group := Group) dSlot → Option → ℝ
  | Sum.inl g => H.jobGroupCoverageWeight members g
  | Sum.inr s => H.residualDeleteWeight lambda (Sum.inr s.1)

/-- Upper rows keep only normalized job deletion. -/
noncomputable def residualJobUpperWeight (lambda : ℕ) : Job → Option → ℝ :=
  fun j o ↦ H.residualDeleteWeight lambda (Sum.inl j) o

@[simp] theorem activeSlotLowerWeight_group
    (members : Group → Finset Job) (lambda dSlot : ℕ)
    (g : Group) (o : Option) :
    H.activeSlotLowerWeight members lambda dSlot (Sum.inl g) o =
      H.jobGroupCoverageWeight members g o := rfl

@[simp] theorem activeSlotLowerWeight_slot
    (members : Group → Finset Job) (lambda dSlot : ℕ)
    (s : H.ActiveSlot dSlot) (o : Option) :
    H.activeSlotLowerWeight members lambda dSlot (Sum.inr s) o =
      H.residualDeleteWeight lambda (Sum.inr s.1) o := rfl

@[simp] theorem residualJobUpperWeight_apply
    (lambda : ℕ) (j : Job) (o : Option) :
    H.residualJobUpperWeight lambda j o =
      H.residualDeleteWeight lambda (Sum.inl j) o := rfl

@[simp] theorem linearRowSupport_activeSlotLowerWeight_group
    (members : Group → Finset Job) (lambda dSlot : ℕ) (g : Group) :
    linearRowSupport (H.activeSlotLowerWeight members lambda dSlot)
        (Sum.inl g) =
      linearRowSupport (H.jobGroupCoverageWeight members) g := rfl

@[simp] theorem linearRowSupport_activeSlotLowerWeight_slot
    (members : Group → Finset Job) (lambda dSlot : ℕ)
    (s : H.ActiveSlot dSlot) :
    linearRowSupport (H.activeSlotLowerWeight members lambda dSlot)
        (Sum.inr s) =
      linearRowSupport (H.residualDeleteWeight lambda) (Sum.inr s.1) := rfl

@[simp] theorem linearRowMean_activeSlotLowerWeight_group
    (q : Option → ℝ) (members : Group → Finset Job)
    (lambda dSlot : ℕ) (g : Group) :
    linearRowMean q (H.activeSlotLowerWeight members lambda dSlot)
        (Sum.inl g) =
      linearRowMean q (H.jobGroupCoverageWeight members) g := rfl

@[simp] theorem linearRowMean_activeSlotLowerWeight_slot
    (q : Option → ℝ) (members : Group → Finset Job)
    (lambda dSlot : ℕ) (s : H.ActiveSlot dSlot) :
    linearRowMean q (H.activeSlotLowerWeight members lambda dSlot)
        (Sum.inr s) =
      linearRowMean q (H.residualDeleteWeight lambda) (Sum.inr s.1) := rfl

@[simp] theorem linearRowSupport_residualJobUpperWeight
    (lambda : ℕ) (j : Job) :
    linearRowSupport (H.residualJobUpperWeight lambda) j =
      linearRowSupport (H.residualDeleteWeight lambda) (Sum.inl j) := rfl

@[simp] theorem linearRowMean_residualJobUpperWeight
    (q : Option → ℝ) (lambda : ℕ) (j : Job) :
    linearRowMean q (H.residualJobUpperWeight lambda) j =
      linearRowMean q (H.residualDeleteWeight lambda) (Sum.inl j) := rfl

theorem activeSlotLowerWeight_nonneg
    (members : Group → Finset Job) (lambda dSlot : ℕ) :
    ∀ r o, 0 ≤ H.activeSlotLowerWeight members lambda dSlot r o := by
  intro r o
  rcases r with g | s
  · exact H.jobGroupCoverageWeight_nonneg members g o
  · exact H.residualDeleteWeight_nonneg lambda (Sum.inr s.1) o

theorem activeSlotLowerWeight_le_one
    (members : Group → Finset Job) (lambda dSlot : ℕ)
    (hlambda : 0 < lambda)
    (hjobSlot : ∀ j s, H.jobSlotCodegree j s ≤ lambda)
    (hslotPair : ∀ s t, s ≠ t → H.slotPairCodegree s t ≤ lambda) :
    ∀ r o, H.activeSlotLowerWeight members lambda dSlot r o ≤ 1 := by
  intro r o
  rcases r with g | s
  · exact H.jobGroupCoverageWeight_le_one members g o
  · exact H.residualDeleteWeight_le_one lambda hlambda hjobSlot hslotPair
      (Sum.inr s.1) o

theorem residualJobUpperWeight_nonneg (lambda : ℕ) :
    ∀ j o, 0 ≤ H.residualJobUpperWeight lambda j o := by
  intro j o
  exact H.residualDeleteWeight_nonneg lambda (Sum.inl j) o

theorem residualJobUpperWeight_le_one
    (lambda : ℕ) (hlambda : 0 < lambda)
    (hjobSlot : ∀ j s, H.jobSlotCodegree j s ≤ lambda)
    (hslotPair : ∀ s t, s ≠ t → H.slotPairCodegree s t ≤ lambda) :
    ∀ j o, H.residualJobUpperWeight lambda j o ≤ 1 := by
  intro j o
  exact H.residualDeleteWeight_le_one lambda hlambda hjobSlot hslotPair
    (Sum.inl j) o

/-- Active slot-row incidence injects into incidence of all residual rows. -/
theorem activeSlotRow_incidence_card_le_residual
    (lambda dSlot : ℕ) (o : Option) :
    (linearRowIncidence
      (fun s : H.ActiveSlot dSlot ↦
        H.residualDeleteWeight lambda (Sum.inr s.1)) o).card ≤
      (linearRowIncidence (H.residualDeleteWeight lambda) o).card := by
  classical
  apply Finset.card_le_card_of_injOn
    (fun s : H.ActiveSlot dSlot ↦ (Sum.inr s.1 : ResidualDeleteRow Job Slot))
  · intro s hs
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_univ _, ?_⟩
    have hs' := (Finset.mem_filter.mp hs).2
    simpa [linearRowSupport] using hs'
  · intro s _hs t _ht hst
    apply Subtype.ext
    exact Sum.inr.inj hst

/-- Job upper-row incidence also injects into incidence of all residual rows. -/
theorem residualJobUpperWeight_incidence_card_le_residual
    (lambda : ℕ) (o : Option) :
    (linearRowIncidence (H.residualJobUpperWeight lambda) o).card ≤
      (linearRowIncidence (H.residualDeleteWeight lambda) o).card := by
  classical
  apply Finset.card_le_card_of_injOn
    (fun j : Job ↦ (Sum.inl j : ResidualDeleteRow Job Slot))
  · intro j hj
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_univ _, ?_⟩
    have hj' := (Finset.mem_filter.mp hj).2
    simpa [linearRowSupport, residualJobUpperWeight] using hj'
  · intro j _hj k _hk hjk
    exact Sum.inl.inj hjk

/-- The combined active lower family has incidence at most `R + 8D`. -/
theorem activeSlotLowerWeight_incidence_card_le
    (members : Group → Finset Job) (lambda dSlot D R : ℕ)
    (hjobDegree : ∀ j, (H.fiber j).card ≤ D)
    (hslotDegree : ∀ s, H.slotDegree s ≤ D)
    (hgroupIncidence : ∀ j,
      ((Finset.univ : Finset Group).filter
        (fun g ↦ j ∈ members g)).card ≤ R)
    (o : Option) :
    (linearRowIncidence
      (H.activeSlotLowerWeight members lambda dSlot) o).card ≤ R + 8 * D := by
  classical
  have hset :
      linearRowIncidence (H.activeSlotLowerWeight members lambda dSlot) o =
        (linearRowIncidence (H.jobGroupCoverageWeight members) o).disjSum
          (linearRowIncidence
            (fun s : H.ActiveSlot dSlot ↦
              H.residualDeleteWeight lambda (Sum.inr s.1)) o) := by
    ext r
    rcases r with g | s
    · simp [linearRowIncidence, linearRowSupport, activeSlotLowerWeight]
    · simp [linearRowIncidence, linearRowSupport, activeSlotLowerWeight]
  rw [hset, Finset.card_disjSum]
  calc
    _ ≤ R + (linearRowIncidence
        (H.residualDeleteWeight lambda) o).card :=
      Nat.add_le_add
        (H.jobGroupCoverage_incidence_card_le members R hgroupIncidence o)
        (H.activeSlotRow_incidence_card_le_residual lambda dSlot o)
    _ ≤ R + 8 * D := Nat.add_le_add_left
      (H.residualDeleteWeight_incidence_card_le_eight_mul
        lambda D hjobDegree hslotDegree o) R

/-- Every job upper family has incidence at most `8D`. -/
theorem residualJobUpperWeight_incidence_card_le
    (lambda D : ℕ)
    (hjobDegree : ∀ j, (H.fiber j).card ≤ D)
    (hslotDegree : ∀ s, H.slotDegree s ≤ D)
    (o : Option) :
    (linearRowIncidence (H.residualJobUpperWeight lambda) o).card ≤ 8 * D :=
  (H.residualJobUpperWeight_incidence_card_le_residual lambda o).trans
    (H.residualDeleteWeight_incidence_card_le_eight_mul
      lambda D hjobDegree hslotDegree o)

/-! ## Separate job and slot scales -/

/-- With job degrees at most `J` and slot degrees at most `S`, one option has
at most `J + 2S` competitors. -/
theorem conflictNeighbors_card_le_job_slot
    (J S : ℕ) (hjobDegree : ∀ j, (H.fiber j).card ≤ J)
    (hslotDegree : ∀ s, H.slotDegree s ≤ S) (o : Option) :
    (H.conflictNeighbors o).card ≤ J + 2 * S := by
  calc
    (H.conflictNeighbors o).card ≤
        (H.fiber (H.owner o) ∪
          (H.slots o).biUnion H.slotOptionFiber).card :=
      Finset.card_le_card (H.conflictNeighbors_subset_owner_union_slots o)
    _ ≤ (H.fiber (H.owner o)).card +
        ((H.slots o).biUnion H.slotOptionFiber).card :=
      Finset.card_union_le _ _
    _ ≤ (H.fiber (H.owner o)).card +
        ∑ s ∈ H.slots o, (H.slotOptionFiber s).card := by
      gcongr
      exact Finset.card_biUnion_le
    _ ≤ J + ∑ _s ∈ H.slots o, S := by
      gcongr with s hs
      · exact hjobDegree (H.owner o)
      · rw [H.slotOptionFiber_card]
        exact hslotDegree s
    _ = J + (H.slots o).card * S := by simp
    _ ≤ J + 2 * S := by
      gcongr
      exact H.slots_card_le_two o

theorem canonicalConflict_incidence_card_le_job_slot
    (J S : ℕ) (hjobDegree : ∀ j, (H.fiber j).card ≤ J)
    (hslotDegree : ∀ s, H.slotDegree s ≤ S) (o : Option) :
    (optionConflictIncidence H.canonicalConflictLeft
      H.canonicalConflictRight o).card ≤ 2 * J + 4 * S := by
  calc
    _ ≤ 2 * (H.conflictNeighbors o).card :=
      H.canonicalConflict_incidence_card_le_two_mul o
    _ ≤ 2 * (J + 2 * S) := Nat.mul_le_mul_left 2
      (H.conflictNeighbors_card_le_job_slot J S hjobDegree hslotDegree o)
    _ = 2 * J + 4 * S := by ring

/-- Slot rows in which `p` occurs are covered by slots used in its owner
fibre or by options meeting `p`. -/
theorem activeSlotRow_incidence_card_le_job_slot
    (lambda dSlot J S : ℕ)
    (hjobDegree : ∀ j, (H.fiber j).card ≤ J)
    (hslotDegree : ∀ s, H.slotDegree s ≤ S) (p : Option) :
    (linearRowIncidence
      (fun s : H.ActiveSlot dSlot ↦
        H.residualDeleteWeight lambda (Sum.inr s.1)) p).card ≤
      2 * J + 4 * S := by
  classical
  let cover : Finset Slot :=
    H.slotsUsedBy (H.fiber (H.owner p)) ∪
      H.slotsUsedBy (H.optionsMeeting p)
  have hmap : (linearRowIncidence
      (fun s : H.ActiveSlot dSlot ↦
        H.residualDeleteWeight lambda (Sum.inr s.1)) p).card ≤
        cover.card := by
    apply Finset.card_le_card_of_injOn (fun s : H.ActiveSlot dSlot ↦ s.1)
    · intro s hs
      have hweight : H.residualDeleteWeight lambda (Sum.inr s.1) p ≠ 0 := by
        simpa [linearRowIncidence, linearRowSupport] using
          (Finset.mem_filter.mp hs).2
      have hc := H.residualDeleteWeight_mem_cover
        lambda p (Sum.inr s.1) hweight
      rcases Finset.mem_union.mp hc with hc | hc
      · rcases Finset.mem_image.mp hc with ⟨a, _ha, heq⟩
        simp at heq
      · rcases Finset.mem_image.mp hc with ⟨t, ht, heq⟩
        have hts : t = s.1 := Sum.inr.inj heq
        simpa [cover, hts] using ht
    · intro s _hs t _ht hst
      exact Subtype.ext hst
  calc
    _ ≤ cover.card := hmap
    _ ≤ (H.slotsUsedBy (H.fiber (H.owner p))).card +
        (H.slotsUsedBy (H.optionsMeeting p)).card := Finset.card_union_le _ _
    _ ≤ 2 * (H.fiber (H.owner p)).card +
        2 * (H.optionsMeeting p).card := Nat.add_le_add
      (H.slotsUsedBy_card_le_two_mul (H.fiber (H.owner p)))
      (H.slotsUsedBy_card_le_two_mul (H.optionsMeeting p))
    _ ≤ 2 * J + 2 * (2 * S) := Nat.add_le_add
      (Nat.mul_le_mul_left 2 (hjobDegree (H.owner p)))
      (Nat.mul_le_mul_left 2
        (H.optionsMeeting_card_le_two_mul S hslotDegree p))
    _ = 2 * J + 4 * S := by ring

/-- Job rows in which `p` occurs are indexed by owners of options meeting
`p`, hence have incidence at most `2S`. -/
theorem residualJobUpperWeight_incidence_card_le_slot
    (lambda S : ℕ) (hslotDegree : ∀ s, H.slotDegree s ≤ S)
    (p : Option) :
    (linearRowIncidence (H.residualJobUpperWeight lambda) p).card ≤
      2 * S := by
  classical
  have hmap : (linearRowIncidence
      (H.residualJobUpperWeight lambda) p).card ≤
      ((H.optionsMeeting p).image H.owner).card := by
    apply Finset.card_le_card_of_injOn (fun j : Job ↦ j)
    · intro j hj
      have hweight : H.residualDeleteWeight lambda (Sum.inl j) p ≠ 0 := by
        simpa [linearRowIncidence, linearRowSupport, residualJobUpperWeight] using
          (Finset.mem_filter.mp hj).2
      have hc := H.residualDeleteWeight_mem_cover lambda p (Sum.inl j) hweight
      rcases Finset.mem_union.mp hc with hc | hc
      · rcases Finset.mem_image.mp hc with ⟨a, ha, heq⟩
        exact Finset.mem_image.mpr ⟨a, ha, Sum.inl.inj heq⟩
      · rcases Finset.mem_image.mp hc with ⟨s, _hs, heq⟩
        simp at heq
    · intro j _hj k _hk hjk
      exact hjk
  calc
    _ ≤ ((H.optionsMeeting p).image H.owner).card := hmap
    _ ≤ (H.optionsMeeting p).card := Finset.card_image_le
    _ ≤ 2 * S := H.optionsMeeting_card_le_two_mul S hslotDegree p

theorem activeSlotLowerWeight_incidence_card_le_job_slot
    (members : Group → Finset Job) (lambda dSlot J S R : ℕ)
    (hjobDegree : ∀ j, (H.fiber j).card ≤ J)
    (hslotDegree : ∀ s, H.slotDegree s ≤ S)
    (hgroupIncidence : ∀ j,
      ((Finset.univ : Finset Group).filter
        (fun g ↦ j ∈ members g)).card ≤ R)
    (o : Option) :
    (linearRowIncidence
      (H.activeSlotLowerWeight members lambda dSlot) o).card ≤
        R + (2 * J + 4 * S) := by
  classical
  have hset :
      linearRowIncidence (H.activeSlotLowerWeight members lambda dSlot) o =
        (linearRowIncidence (H.jobGroupCoverageWeight members) o).disjSum
          (linearRowIncidence
            (fun s : H.ActiveSlot dSlot ↦
              H.residualDeleteWeight lambda (Sum.inr s.1)) o) := by
    ext r
    rcases r with g | s
    · simp [linearRowIncidence, linearRowSupport, activeSlotLowerWeight]
    · simp [linearRowIncidence, linearRowSupport, activeSlotLowerWeight]
  rw [hset, Finset.card_disjSum]
  exact Nat.add_le_add
    (H.jobGroupCoverage_incidence_card_le members R hgroupIncidence o)
    (H.activeSlotRow_incidence_card_le_job_slot
      lambda dSlot J S hjobDegree hslotDegree o)

/-- Active slot-row support with separate job and slot maxima. -/
theorem activeSlot_support_card_le_job_slot
    (lambda J S : ℕ) (hjobDegree : ∀ j, (H.fiber j).card ≤ J)
    (hslotDegree : ∀ s, H.slotDegree s ≤ S) (s : Slot) :
    (linearRowSupport (H.residualDeleteWeight lambda) (Sum.inr s)).card ≤
      S * (J + 2 * S) := by
  apply (Finset.card_le_card
    (H.residualDeleteWeight_slot_support_subset lambda s)).trans
  calc
    (H.slotDeleteRowCover s).card ≤
        ∑ o ∈ H.slotOptionFiber s,
          (H.fiber (H.owner o) ∪ H.optionsMeeting o).card :=
      Finset.card_biUnion_le
    _ ≤ ∑ o ∈ H.slotOptionFiber s,
        ((H.fiber (H.owner o)).card + (H.optionsMeeting o).card) := by
      exact Finset.sum_le_sum fun o _ ↦ Finset.card_union_le _ _
    _ ≤ ∑ _o ∈ H.slotOptionFiber s, (J + 2 * S) := by
      apply Finset.sum_le_sum
      intro o _
      exact Nat.add_le_add (hjobDegree (H.owner o))
        (H.optionsMeeting_card_le_two_mul S hslotDegree o)
    _ = (H.slotOptionFiber s).card * (J + 2 * S) := by simp
    _ ≤ S * (J + 2 * S) := by
      apply Nat.mul_le_mul_right
      rw [H.slotOptionFiber_card]
      exact hslotDegree s

/-- Job upper-row support with separate job and slot maxima. -/
theorem residualJobUpper_support_card_le_job_slot
    (lambda J S : ℕ) (hjobDegree : ∀ j, (H.fiber j).card ≤ J)
    (hslotDegree : ∀ s, H.slotDegree s ≤ S) (j : Job) :
    (linearRowSupport (H.residualJobUpperWeight lambda) j).card ≤
      2 * J * S := by
  change (linearRowSupport (H.residualDeleteWeight lambda) (Sum.inl j)).card ≤
    2 * J * S
  calc
    _ ≤ (H.externalJobRowCover j).card := Finset.card_le_card
      (H.residualDeleteWeight_job_support_subset lambda j)
    _ ≤ (H.fiber j).card * (2 * S) :=
      H.externalJobRowCover_card_le_degree S hslotDegree j
    _ ≤ J * (2 * S) := Nat.mul_le_mul_right (2 * S) (hjobDegree j)
    _ = 2 * J * S := by ring

/-! ## Exact active-slot Harris bridge -/

/-- A Harris round with lower deletion only at active slots and upper
deletion only on job rows.  All support-incidence conditions are discharged;
the three tail families remain as explicit numeric hypotheses. -/
theorem exists_oneRound_activeSlot_harris
    (q : Option → ℝ) (members : Group → Finset Job)
    (lambda : ℕ) (hlambda : 0 < lambda) (dSlot : ℕ)
    (groupThreshold groupLambda : Group → ℝ)
    (slotThreshold slotLambda : H.ActiveSlot dSlot → ℝ)
    (upperJobBudget : Job → ℕ) (jobLambda : Job → ℝ)
    (J S R : ℕ) (pairX rowX cap : ℝ)
    (hq0 : ∀ o, 0 ≤ q o) (hq1 : ∀ o, q o ≤ 1)
    (hjobDegree : ∀ j, (H.fiber j).card ≤ J)
    (hslotDegree : ∀ s, H.slotDegree s ≤ S)
    (hjobSlot : ∀ j s, H.jobSlotCodegree j s ≤ lambda)
    (hslotPair : ∀ s t, s ≠ t → H.slotPairCodegree s t ≤ lambda)
    (hgroupIncidence : ∀ j,
      ((Finset.univ : Finset Group).filter
        (fun g ↦ j ∈ members g)).card ≤ R)
    (hgroupLambda : ∀ g, 0 ≤ groupLambda g)
    (hslotLambda : ∀ s, 0 ≤ slotLambda s)
    (hjobLambda : ∀ j, 0 ≤ jobLambda j)
    (hpairX0 : 0 ≤ pairX) (hrowX0 : 0 ≤ rowX)
    (hpairXcap : pairX ≤ cap) (hrowXcap : rowX ≤ cap)
    (hcap1 : cap < 1)
    (hpair : ∀ c : H.ConflictIndex,
      q (H.canonicalConflictLeft c) * q (H.canonicalConflictRight c) ≤
        pairX * (1 - rowX) ^ (2 * (R + (2 * J + 4 * S))))
    (hgroupLower : ∀ g,
      Real.exp (groupLambda g * groupThreshold g +
          (Real.exp (-groupLambda g) - 1) *
            linearRowMean q (H.jobGroupCoverageWeight members) g) ≤
        rowX * (1 - cap) ^
          ((linearRowSupport
            (H.jobGroupCoverageWeight members) g).card * (2 * J + 6 * S)))
    (hslotLower : ∀ s,
      Real.exp (slotLambda s * slotThreshold s +
          (Real.exp (-slotLambda s) - 1) *
            linearRowMean q (H.residualDeleteWeight lambda) (Sum.inr s.1)) ≤
        rowX * (1 - cap) ^
          ((linearRowSupport (H.residualDeleteWeight lambda)
            (Sum.inr s.1)).card * (2 * J + 6 * S)))
    (hjobUpper : ∀ j,
      Real.exp (-jobLambda j *
          ((upperJobBudget j : ℝ) / (2 * lambda : ℕ)) +
        (Real.exp (jobLambda j) - 1) *
          linearRowMean q (H.residualDeleteWeight lambda) (Sum.inl j)) ≤
        rowX * (1 - rowX) ^
          ((linearRowSupport (H.residualDeleteWeight lambda)
            (Sum.inl j)).card * (R + (2 * J + 4 * S)))) :
    ∃ S : Finset Option,
      H.IsPartialMatching S ∧
      (∀ g, groupThreshold g <
        (H.coveredGroupJobs members g S).card) ∧
      (∀ s : H.ActiveSlot dSlot,
        (∀ p ∈ S, s.1 ∉ H.slots p) →
          slotThreshold s <
            H.slotDeletionLoad S s.1 / (3 * lambda : ℕ)) ∧
      (∀ j, ¬ H.Covers S j →
        H.residualJobDegree ∅ j ≤
          H.residualJobDegree S j + upperJobBudget j) := by
  let lowerThreshold : H.ActiveSlotLowerRow (Group := Group) dSlot → ℝ
    | Sum.inl g => groupThreshold g
    | Sum.inr s => slotThreshold s
  let lowerLambda : H.ActiveSlotLowerRow (Group := Group) dSlot → ℝ
    | Sum.inl g => groupLambda g
    | Sum.inr s => slotLambda s
  let upperThreshold : Job → ℝ :=
    fun j ↦ (upperJobBudget j : ℝ) / (2 * lambda : ℕ)
  have hlowerLambda : ∀ r, 0 ≤ lowerLambda r := by
    intro r
    rcases r with g | s
    · exact hgroupLambda g
    · exact hslotLambda s
  have hlowerNumeric : ∀ r,
      Real.exp (lowerLambda r * lowerThreshold r +
          (Real.exp (-lowerLambda r) - 1) *
            linearRowMean q
              (H.activeSlotLowerWeight members lambda dSlot) r) ≤
        rowX * (1 - cap) ^
          ((linearRowSupport
            (H.activeSlotLowerWeight members lambda dSlot) r).card *
              ((2 * J + 4 * S) + 2 * S)) := by
    have hsum : (2 * J + 4 * S) + 2 * S = 2 * J + 6 * S := by omega
    intro r
    rcases r with g | s
    · simpa [lowerLambda, lowerThreshold, hsum] using hgroupLower g
    · simpa [lowerLambda, lowerThreshold, hsum] using hslotLower s
  have hupperNumeric : ∀ j,
      Real.exp (-jobLambda j * upperThreshold j +
          (Real.exp (jobLambda j) - 1) *
            linearRowMean q (H.residualJobUpperWeight lambda) j) ≤
        rowX * (1 - rowX) ^
          ((linearRowSupport (H.residualJobUpperWeight lambda) j).card *
            (R + (2 * J + 4 * S))) := by
    intro j
    simpa [upperThreshold] using hjobUpper j
  rcases H.exists_partialMatching_with_lower_and_upper_rows_harris_of_incidence
      H.canonicalConflictLeft H.canonicalConflictRight q
      (H.activeSlotLowerWeight members lambda dSlot)
      (H.residualJobUpperWeight lambda)
      lowerThreshold lowerLambda upperThreshold jobLambda
      H.canonicalConflict_ne H.canonicalConflict_complete
      (2 * J + 4 * S) (R + (2 * J + 4 * S)) (2 * S)
      pairX rowX cap
      hq0 hq1
      (H.activeSlotLowerWeight_nonneg members lambda dSlot)
      (H.activeSlotLowerWeight_le_one members lambda dSlot hlambda
        hjobSlot hslotPair)
      (H.residualJobUpperWeight_nonneg lambda)
      (H.residualJobUpperWeight_le_one lambda hlambda hjobSlot hslotPair)
      hlowerLambda hjobLambda hpairX0 hrowX0 hpairXcap hrowXcap hcap1
      (H.canonicalConflict_incidence_card_le_job_slot
        J S hjobDegree hslotDegree)
      (H.activeSlotLowerWeight_incidence_card_le_job_slot
        members lambda dSlot J S R
        hjobDegree hslotDegree hgroupIncidence)
      (H.residualJobUpperWeight_incidence_card_le_slot
        lambda S hslotDegree)
      hpair hlowerNumeric hupperNumeric with
    ⟨S, hS, hlower, hupper⟩
  have hgroup : ∀ g, groupThreshold g <
      (H.coveredGroupJobs members g S).card := by
    intro g
    apply H.coveredGroupJobs_count_gt_of_row_gt members g S hS
    have h := hlower (Sum.inl g)
    rw [weightedSum_linearRowSupport
      (H.activeSlotLowerWeight members lambda dSlot) (Sum.inl g) S] at h
    simpa [lowerThreshold, activeSlotLowerWeight] using h
  have hslot : ∀ s : H.ActiveSlot dSlot,
      (∀ p ∈ S, s.1 ∉ H.slots p) → slotThreshold s <
        H.slotDeletionLoad S s.1 / (3 * lambda : ℕ) := by
    intro s hunused
    have h := hlower (Sum.inr s)
    rw [weightedSum_linearRowSupport
      (H.activeSlotLowerWeight members lambda dSlot) (Sum.inr s) S] at h
    change slotThreshold s <
      ∑ o ∈ S, H.residualDeleteWeight lambda (Sum.inr s.1) o at h
    rw [H.selected_residualDeleteWeight_slot lambda S s.1 hunused] at h
    exact h
  have hjob : ∀ j, ¬ H.Covers S j →
      H.residualJobDegree ∅ j ≤
        H.residualJobDegree S j + upperJobBudget j := by
    intro j huncovered
    have hnorm := hupper j
    rw [weightedSum_linearRowSupport
      (H.residualJobUpperWeight lambda) j S] at hnorm
    change (∑ o ∈ S,
      H.residualDeleteWeight lambda (Sum.inl j) o) <
        (upperJobBudget j : ℝ) / (2 * lambda : ℕ) at hnorm
    rw [H.selected_residualDeleteWeight_job lambda S j] at hnorm
    have hden : (0 : ℝ) < (2 * lambda : ℕ) := by positivity
    have hcast : (H.externalJobDeletionLoad S j : ℝ) <
        upperJobBudget j := by
      exact (div_lt_div_iff_of_pos_right hden).mp hnorm
    have hload : H.externalJobDeletionLoad S j < upperJobBudget j := by
      exact_mod_cast hcast
    have hremoved :=
      H.removedResidualFiber_empty_card_le_externalJobDeletionLoad
        S j huncovered
    have hidentity := H.residualJobDegree_union_add_removed ∅ S j
    simp only [Finset.empty_union] at hidentity
    omega
  exact ⟨S, hS, hgroup, hslot, hjob⟩

/-! ## Uniform means and a scalar specialization -/

/-- A common lower mean for group rows and active slot-deletion rows. -/
noncomputable def activeSlotUniformLowerMean
    (rho : ℝ) (m dJob dSlot lambda : ℕ) : ℝ :=
  min (rho * (m : ℝ))
    (rho * (((dSlot * (dJob - lambda) : ℕ) : ℝ) /
      ((3 * lambda : ℕ) : ℝ)))

theorem activeSlotUniformLowerMean_nonneg
    (rho : ℝ) (m dJob dSlot lambda : ℕ) (hrho0 : 0 ≤ rho) :
    0 ≤ activeSlotUniformLowerMean rho m dJob dSlot lambda := by
  apply le_min
  · exact mul_nonneg hrho0 (Nat.cast_nonneg m)
  · exact mul_nonneg hrho0
      (div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _))

theorem activeSlotUniformLowerMean_le_groupMean
    (rho : ℝ) (members : Group → Finset Job)
    (m dJob dSlot lambda : ℕ) (hrho0 : 0 ≤ rho)
    (hgroupSupportLower : ∀ g,
      m ≤ (linearRowSupport
        (H.jobGroupCoverageWeight members) g).card) (g : Group) :
    activeSlotUniformLowerMean rho m dJob dSlot lambda ≤
      linearRowMean (fun _ : Option ↦ rho)
        (H.jobGroupCoverageWeight members) g := by
  calc
    activeSlotUniformLowerMean rho m dJob dSlot lambda ≤
        rho * (m : ℝ) := min_le_left _ _
    _ ≤ rho *
        ((linearRowSupport
          (H.jobGroupCoverageWeight members) g).card : ℝ) := by
      apply mul_le_mul_of_nonneg_left _ hrho0
      exact_mod_cast hgroupSupportLower g
    _ = linearRowMean (fun _ : Option ↦ rho)
        (H.jobGroupCoverageWeight members) g := by
      rw [H.linearRowMean_jobGroupCoverageWeight_uniform]

/-- Only the selected slot must have large degree.  No lower bound is imposed
on inactive slot rows. -/
theorem activeSlotUniformLowerMean_le_slotMean
    (rho : ℝ) (lambda dJob dSlot m : ℕ) (hlambda : 0 < lambda)
    (hrho0 : 0 ≤ rho)
    (hjobDegreeLower : ∀ o, dJob ≤ (H.fiber (H.owner o)).card)
    (hjobSlot : ∀ j s, H.jobSlotCodegree j s ≤ lambda)
    (s : H.ActiveSlot dSlot) :
    activeSlotUniformLowerMean rho m dJob dSlot lambda ≤
      linearRowMean (fun _ : Option ↦ rho)
        (H.residualDeleteWeight lambda) (Sum.inr s.1) := by
  have hlocal := H.residualDeleteWeight_slot_mean_ge_of_owners
    rho s.1 dJob lambda hlambda hrho0
      (fun o _hos ↦ hjobDegreeLower o)
      (fun j ↦ hjobSlot j s.1)
  apply le_trans (min_le_right _ _) (le_trans ?_ hlocal)
  apply mul_le_mul_of_nonneg_left ?_ hrho0
  apply div_le_div_of_nonneg_right
  · exact_mod_cast Nat.mul_le_mul_right (dJob - lambda) s.2
  · exact Nat.cast_nonneg _

/-- Half-tail estimate when both the threshold and a lower bound for the
actual mean are replaced by one common floor `eta`. -/
theorem half_lowerTail_exp_le_of_floor
    (eta threshold mu : ℝ) (heta0 : 0 ≤ eta)
    (hthreshold : threshold ≤ eta / 2) (hmean : eta ≤ mu) :
    Real.exp ((1 / 2 : ℝ) * threshold +
        (Real.exp (-(1 / 2 : ℝ)) - 1) * mu) ≤
      Real.exp (-(1 / 8 : ℝ) * eta) := by
  apply Real.exp_le_exp.mpr
  have hcoef : Real.exp (-(1 / 2 : ℝ)) - 1 ≤ 0 := by
    apply sub_nonpos.mpr
    exact Real.exp_le_one_iff.mpr (by norm_num)
  calc
    (1 / 2 : ℝ) * threshold +
        (Real.exp (-(1 / 2 : ℝ)) - 1) * mu ≤
      (1 / 2 : ℝ) * (eta / 2) +
        (Real.exp (-(1 / 2 : ℝ)) - 1) * eta :=
      add_le_add
        (mul_le_mul_of_nonneg_left hthreshold (by norm_num))
        (mul_le_mul_of_nonpos_left hmean hcoef)
    _ = ((1 / 2 : ℝ) * (1 - 1 / 2) +
        (Real.exp (-(1 / 2 : ℝ)) - 1)) * eta := by ring
    _ ≤ -(1 / 8 : ℝ) * eta :=
      half_lowerTail_exponent_le eta heta0

/-- Uniform active-slot round with all local-lemma products kept at their
natural exponential scale.  Its assumptions consist of degree/codegree
bounds, two budget comparisons, and three global scalar LLL inequalities. -/
theorem exists_oneRound_activeSlot_uniform_exponential
    (rho : ℝ) (members : Group → Finset Job)
    (lambda : ℕ) (hlambda : 0 < lambda)
    (lowerSlotBudget : Slot → ℕ) (upperJobBudget : Job → ℕ)
    (J S dJob dSlot R K m : ℕ) (pairX rowX cap : ℝ)
    (hrho0 : 0 ≤ rho) (hrho1 : rho ≤ 1)
    (hjobDegreeLower : ∀ o, dJob ≤ (H.fiber (H.owner o)).card)
    (hjobDegreeUpper : ∀ j, (H.fiber j).card ≤ J)
    (hslotDegreeUpper : ∀ s, H.slotDegree s ≤ S)
    (hjobSlot : ∀ j s, H.jobSlotCodegree j s ≤ lambda)
    (hslotPair : ∀ s t, s ≠ t → H.slotPairCodegree s t ≤ lambda)
    (hmembers : ∀ g, (members g).card ≤ K)
    (hgroupSupportLower : ∀ g,
      m ≤ (linearRowSupport
        (H.jobGroupCoverageWeight members) g).card)
    (hgroupIncidence : ∀ j,
      ((Finset.univ : Finset Group).filter
        (fun g ↦ j ∈ members g)).card ≤ R)
    (hpairX0 : 0 ≤ pairX) (hrowX0 : 0 ≤ rowX)
    (hpairXcap : pairX ≤ cap) (hrowXcap : rowX ≤ cap)
    (hcapHalf : cap ≤ 1 / 2)
    (hlowerSlotThreshold : ∀ s : H.ActiveSlot dSlot,
      (lowerSlotBudget s.1 : ℝ) / (3 * lambda : ℕ) ≤
        activeSlotUniformLowerMean rho m dJob dSlot lambda / 2)
    (hupperJobThreshold : ∀ j,
      4 * (rho * ((J : ℝ) * (S : ℝ) / (lambda : ℝ))) ≤
        (upperJobBudget j : ℝ) / (2 * lambda : ℕ))
    (hpairNumeric : rho * rho ≤
      pairX * Real.exp
        (-2 * rowX * ((2 * (R + (2 * J + 4 * S)) : ℕ) : ℝ)))
    (hlowerNumeric :
      Real.exp (-(1 / 8 : ℝ) *
          activeSlotUniformLowerMean rho m dJob dSlot lambda) ≤
        rowX * Real.exp
          (-2 * cap *
            (((Nat.max (K * J) (S * (J + 2 * S))) *
              (2 * J + 6 * S) : ℕ) : ℝ)))
    (hupperNumeric :
      Real.exp (-2 *
          (rho * ((J : ℝ) * (S : ℝ) / (lambda : ℝ)))) ≤
        rowX * Real.exp
          (-2 * rowX *
            (((2 * J * S) * (R + (2 * J + 4 * S)) : ℕ) : ℝ))) :
    ∃ S : Finset Option,
      H.IsPartialMatching S ∧
      (∀ g,
        activeSlotUniformLowerMean rho m dJob dSlot lambda / 2 <
          (H.coveredGroupJobs members g S).card) ∧
      (∀ s : H.ActiveSlot dSlot,
        (∀ p ∈ S, s.1 ∉ H.slots p) →
          2 * H.residualSlotDegree S s.1 + lowerSlotBudget s.1 ≤
            2 * H.residualSlotDegree ∅ s.1) ∧
      (∀ j, ¬ H.Covers S j →
        H.residualJobDegree ∅ j ≤
          H.residualJobDegree S j + upperJobBudget j) := by
  let eta : ℝ := activeSlotUniformLowerMean rho m dJob dSlot lambda
  let muUpper : ℝ :=
    rho * ((J : ℝ) * (S : ℝ) / (lambda : ℝ))
  let maxSupport : ℕ := Nat.max (K * J) (S * (J + 2 * S))
  have heta0 : 0 ≤ eta := by
    exact activeSlotUniformLowerMean_nonneg rho m dJob dSlot lambda hrho0
  have hmuUpper0 : 0 ≤ muUpper := by
    dsimp [muUpper]
    exact mul_nonneg hrho0
      (div_nonneg
        (mul_nonneg (Nat.cast_nonneg J) (Nat.cast_nonneg S))
        (Nat.cast_nonneg lambda))
  have hcap0 : 0 ≤ cap := hpairX0.trans hpairXcap
  have hrowHalf : rowX ≤ 1 / 2 := hrowXcap.trans hcapHalf
  have hcap1 : cap < 1 := hcapHalf.trans_lt (by norm_num)
  have hpairPow : rho * rho ≤
      pairX * (1 - rowX) ^ (2 * (R + (2 * J + 4 * S))) := by
    apply hpairNumeric.trans
    apply mul_le_mul_of_nonneg_left _ hpairX0
    exact WeightedEdgeColoring.exp_neg_two_mul_nat_le_one_sub_pow rowX
      (2 * (R + (2 * J + 4 * S))) hrowX0 hrowHalf
  have hgroupTail : ∀ g,
      Real.exp ((1 / 2 : ℝ) * (eta / 2) +
          (Real.exp (-(1 / 2 : ℝ)) - 1) *
            linearRowMean (fun _ : Option ↦ rho)
              (H.jobGroupCoverageWeight members) g) ≤
        rowX * (1 - cap) ^
          ((linearRowSupport
            (H.jobGroupCoverageWeight members) g).card *
              (2 * J + 6 * S)) := by
    intro g
    have hmean : eta ≤
        linearRowMean (fun _ : Option ↦ rho)
          (H.jobGroupCoverageWeight members) g := by
      simpa [eta] using H.activeSlotUniformLowerMean_le_groupMean
        rho members m dJob dSlot lambda hrho0 hgroupSupportLower g
    have htail := half_lowerTail_exp_le_of_floor eta (eta / 2)
      (linearRowMean (fun _ : Option ↦ rho)
        (H.jobGroupCoverageWeight members) g) heta0 le_rfl hmean
    have hs : (linearRowSupport
        (H.jobGroupCoverageWeight members) g).card ≤ maxSupport :=
      (H.jobGroupCoverage_support_card_le members K J
        hmembers hjobDegreeUpper g).trans (Nat.le_max_left _ _)
    have hdegree : (linearRowSupport
        (H.jobGroupCoverageWeight members) g).card * (2 * J + 6 * S) ≤
          maxSupport * (2 * J + 6 * S) :=
      Nat.mul_le_mul_right (2 * J + 6 * S) hs
    have hexp : Real.exp
        (-2 * cap * ((maxSupport * (2 * J + 6 * S) : ℕ) : ℝ)) ≤
          (1 - cap) ^ (maxSupport * (2 * J + 6 * S)) :=
      WeightedEdgeColoring.exp_neg_two_mul_nat_le_one_sub_pow cap
        (maxSupport * (2 * J + 6 * S)) hcap0 hcapHalf
    have hpow : (1 - cap) ^ (maxSupport * (2 * J + 6 * S)) ≤
        (1 - cap) ^
          ((linearRowSupport
            (H.jobGroupCoverageWeight members) g).card *
              (2 * J + 6 * S)) :=
      pow_le_pow_of_le_one (sub_nonneg.mpr hcap1.le)
        (sub_le_self 1 hcap0) hdegree
    calc
      _ ≤ Real.exp (-(1 / 8 : ℝ) * eta) := htail
      _ ≤ rowX * Real.exp
          (-2 * cap *
            ((maxSupport * (2 * J + 6 * S) : ℕ) : ℝ)) := by
        simpa [eta, maxSupport] using hlowerNumeric
      _ ≤ rowX * (1 - cap) ^ (maxSupport * (2 * J + 6 * S)) :=
        mul_le_mul_of_nonneg_left hexp hrowX0
      _ ≤ rowX * (1 - cap) ^
          ((linearRowSupport
            (H.jobGroupCoverageWeight members) g).card *
              (2 * J + 6 * S)) :=
        mul_le_mul_of_nonneg_left hpow hrowX0
  have hslotTail : ∀ s : H.ActiveSlot dSlot,
      Real.exp ((1 / 2 : ℝ) *
          ((lowerSlotBudget s.1 : ℝ) / (3 * lambda : ℕ)) +
        (Real.exp (-(1 / 2 : ℝ)) - 1) *
          linearRowMean (fun _ : Option ↦ rho)
            (H.residualDeleteWeight lambda) (Sum.inr s.1)) ≤
        rowX * (1 - cap) ^
          ((linearRowSupport (H.residualDeleteWeight lambda)
            (Sum.inr s.1)).card * (2 * J + 6 * S)) := by
    intro s
    have hmean : eta ≤
        linearRowMean (fun _ : Option ↦ rho)
          (H.residualDeleteWeight lambda) (Sum.inr s.1) := by
      simpa [eta] using H.activeSlotUniformLowerMean_le_slotMean
        rho lambda dJob dSlot m hlambda hrho0 hjobDegreeLower hjobSlot s
    have htail := half_lowerTail_exp_le_of_floor eta
      ((lowerSlotBudget s.1 : ℝ) / (3 * lambda : ℕ))
      (linearRowMean (fun _ : Option ↦ rho)
        (H.residualDeleteWeight lambda) (Sum.inr s.1)) heta0
      (by simpa [eta] using hlowerSlotThreshold s) hmean
    have hs0 := H.activeSlot_support_card_le_job_slot
      lambda J S hjobDegreeUpper hslotDegreeUpper s.1
    have hs : (linearRowSupport (H.residualDeleteWeight lambda)
        (Sum.inr s.1)).card ≤ maxSupport :=
      hs0.trans (Nat.le_max_right _ _)
    have hdegree : (linearRowSupport (H.residualDeleteWeight lambda)
        (Sum.inr s.1)).card * (2 * J + 6 * S) ≤
          maxSupport * (2 * J + 6 * S) :=
      Nat.mul_le_mul_right (2 * J + 6 * S) hs
    have hexp : Real.exp
        (-2 * cap * ((maxSupport * (2 * J + 6 * S) : ℕ) : ℝ)) ≤
          (1 - cap) ^ (maxSupport * (2 * J + 6 * S)) :=
      WeightedEdgeColoring.exp_neg_two_mul_nat_le_one_sub_pow cap
        (maxSupport * (2 * J + 6 * S)) hcap0 hcapHalf
    have hpow : (1 - cap) ^ (maxSupport * (2 * J + 6 * S)) ≤
        (1 - cap) ^
          ((linearRowSupport (H.residualDeleteWeight lambda)
            (Sum.inr s.1)).card * (2 * J + 6 * S)) :=
      pow_le_pow_of_le_one (sub_nonneg.mpr hcap1.le)
        (sub_le_self 1 hcap0) hdegree
    calc
      _ ≤ Real.exp (-(1 / 8 : ℝ) * eta) := htail
      _ ≤ rowX * Real.exp
          (-2 * cap *
            ((maxSupport * (2 * J + 6 * S) : ℕ) : ℝ)) := by
        simpa [eta, maxSupport] using hlowerNumeric
      _ ≤ rowX * (1 - cap) ^ (maxSupport * (2 * J + 6 * S)) :=
        mul_le_mul_of_nonneg_left hexp hrowX0
      _ ≤ rowX * (1 - cap) ^
          ((linearRowSupport (H.residualDeleteWeight lambda)
            (Sum.inr s.1)).card * (2 * J + 6 * S)) :=
        mul_le_mul_of_nonneg_left hpow hrowX0
  have hjobTail : ∀ j,
      Real.exp (-(1 : ℝ) *
          ((upperJobBudget j : ℝ) / (2 * lambda : ℕ)) +
        (Real.exp (1 : ℝ) - 1) *
          linearRowMean (fun _ : Option ↦ rho)
            (H.residualDeleteWeight lambda) (Sum.inl j)) ≤
        rowX * (1 - rowX) ^
          ((linearRowSupport (H.residualDeleteWeight lambda)
            (Sum.inl j)).card * (R + (2 * J + 4 * S))) := by
    intro j
    have hmean : linearRowMean (fun _ : Option ↦ rho)
        (H.residualDeleteWeight lambda) (Sum.inl j) ≤ muUpper := by
      have hlocal := H.residualDeleteWeight_job_mean_le_degree
        rho lambda S hlambda hrho0 j hslotDegreeUpper
      apply hlocal.trans
      apply mul_le_mul_of_nonneg_left ?_ hrho0
      apply div_le_div_of_nonneg_right
      · exact mul_le_mul_of_nonneg_right
          (by exact_mod_cast hjobDegreeUpper j) (Nat.cast_nonneg S)
      · exact Nat.cast_nonneg _
    have hcoef : 0 ≤ Real.exp (1 : ℝ) - 1 :=
      sub_nonneg.mpr (Real.one_le_exp (by norm_num))
    have hfirst : Real.exp (-(1 : ℝ) *
          ((upperJobBudget j : ℝ) / (2 * lambda : ℕ)) +
        (Real.exp (1 : ℝ) - 1) *
          linearRowMean (fun _ : Option ↦ rho)
            (H.residualDeleteWeight lambda) (Sum.inl j)) ≤
        Real.exp (-((upperJobBudget j : ℝ) / (2 * lambda : ℕ)) +
          (Real.exp 1 - 1) * muUpper) := by
      apply Real.exp_le_exp.mpr
      have hmul := mul_le_mul_of_nonneg_left hmean hcoef
      norm_num
      linarith
    have htail : Real.exp
        (-((upperJobBudget j : ℝ) / (2 * lambda : ℕ)) +
          (Real.exp 1 - 1) * muUpper) ≤ Real.exp (-2 * muUpper) :=
      upperTail_lambda_one_exp_le muUpper
        ((upperJobBudget j : ℝ) / (2 * lambda : ℕ)) hmuUpper0
        (by simpa [muUpper] using hupperJobThreshold j)
    have hs := H.residualJobUpper_support_card_le_job_slot
      lambda J S hjobDegreeUpper hslotDegreeUpper j
    have hdegree : (linearRowSupport (H.residualDeleteWeight lambda)
        (Sum.inl j)).card * (R + (2 * J + 4 * S)) ≤
          (2 * J * S) * (R + (2 * J + 4 * S)) :=
      Nat.mul_le_mul_right (R + (2 * J + 4 * S)) hs
    have hexp : Real.exp
        (-2 * rowX *
          (((2 * J * S) * (R + (2 * J + 4 * S)) : ℕ) : ℝ)) ≤
          (1 - rowX) ^ ((2 * J * S) * (R + (2 * J + 4 * S))) :=
      WeightedEdgeColoring.exp_neg_two_mul_nat_le_one_sub_pow rowX
        ((2 * J * S) * (R + (2 * J + 4 * S))) hrowX0 hrowHalf
    have hpow :
        (1 - rowX) ^ ((2 * J * S) * (R + (2 * J + 4 * S))) ≤
        (1 - rowX) ^
          ((linearRowSupport (H.residualDeleteWeight lambda)
            (Sum.inl j)).card * (R + (2 * J + 4 * S))) :=
      pow_le_pow_of_le_one
        (sub_nonneg.mpr (hrowHalf.trans (by norm_num)))
        (sub_le_self 1 hrowX0) hdegree
    calc
      _ ≤ Real.exp (-2 * muUpper) := hfirst.trans htail
      _ ≤ rowX * Real.exp
          (-2 * rowX *
            (((2 * J * S) * (R + (2 * J + 4 * S)) : ℕ) : ℝ)) := by
        simpa [muUpper] using hupperNumeric
      _ ≤ rowX * (1 - rowX) ^
          ((2 * J * S) * (R + (2 * J + 4 * S))) :=
        mul_le_mul_of_nonneg_left hexp hrowX0
      _ ≤ rowX * (1 - rowX) ^
          ((linearRowSupport (H.residualDeleteWeight lambda)
            (Sum.inl j)).card * (R + (2 * J + 4 * S))) :=
        mul_le_mul_of_nonneg_left hpow hrowX0
  rcases H.exists_oneRound_activeSlot_harris
      (fun _ : Option ↦ rho) members lambda hlambda dSlot
      (fun _ ↦ eta / 2) (fun _ ↦ (1 / 2 : ℝ))
      (fun s ↦ (lowerSlotBudget s.1 : ℝ) / (3 * lambda : ℕ))
      (fun _ ↦ (1 / 2 : ℝ)) upperJobBudget (fun _ ↦ (1 : ℝ))
      J S R pairX rowX cap (fun _ ↦ hrho0) (fun _ ↦ hrho1)
      hjobDegreeUpper hslotDegreeUpper hjobSlot hslotPair hgroupIncidence
      (fun _ ↦ by norm_num) (fun _ ↦ by norm_num)
      (fun _ ↦ by norm_num) hpairX0 hrowX0 hpairXcap hrowXcap hcap1
      (fun _ ↦ hpairPow) hgroupTail hslotTail hjobTail with
    ⟨S, hS, hgroup, hslotLower, hjobUpper⟩
  have hslotShrink : ∀ s : H.ActiveSlot dSlot,
      (∀ p ∈ S, s.1 ∉ H.slots p) →
        2 * H.residualSlotDegree S s.1 + lowerSlotBudget s.1 ≤
          2 * H.residualSlotDegree ∅ s.1 := by
    intro s hunused
    have hden : (0 : ℝ) < (3 * lambda : ℕ) := by positivity
    have hcast : (lowerSlotBudget s.1 : ℝ) <
        H.slotDeletionLoad S s.1 := by
      apply (div_lt_div_iff_of_pos_right hden).mp
      exact hslotLower s hunused
    have hnat : lowerSlotBudget s.1 ≤ H.slotDeletionLoad S s.1 := by
      have : lowerSlotBudget s.1 < H.slotDeletionLoad S s.1 := by
        exact_mod_cast hcast
      omega
    exact H.two_mul_residualSlotDegree_add_linearLower_le
      S s.1 hS hunused (lowerSlotBudget s.1) hnat
  refine ⟨S, hS, ?_, hslotShrink, hjobUpper⟩
  simpa [eta] using hgroup

end WeightedEdgeColoring.RankThreeOptionSystem
