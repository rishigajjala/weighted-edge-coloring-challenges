import WeightedEdgeColoring.RankThreeResidualHarrisBridge
import WeightedEdgeColoring.RankThreeGroupCoverageBridge
import WeightedEdgeColoring.RankThreeResidualCollisionHalf

/-!
# A two-sided residual Harris round

The usual residual round asks for a lower bound on group coverage and upper
bounds on the linear deletion rows.  For iteration it is also useful to force
every residual deletion row to be large.  This file puts the group rows and a
second copy of the residual rows into one disjoint sum of lower-tail rows.

The resulting theorem is genuinely simultaneous: one partial matching covers
all declared job groups, gives lower bounds on the normalized job and slot
deletion loads, and retains the earlier upper residual-degree guarantees.  All
rank-three support-incidence estimates are discharged here.  The remaining
hypotheses are the explicit Chernoff--Harris inequalities for the chosen
numeric parameters.
-/

namespace WeightedEdgeColoring.RankThreeOptionSystem

open scoped BigOperators
open WeightedEdgeColoring.FiniteBernoulliSupportSplit

universe u v w x

variable {Job : Type u} {Slot : Type v} {Option : Type w} {Group : Type x}
  [Fintype Job] [Fintype Slot] [Fintype Option] [Fintype Group]
  [DecidableEq Job] [DecidableEq Slot] [DecidableEq Option] [DecidableEq Group]
  (H : RankThreeOptionSystem Job Slot Option)

/-- The lower-tail rows in a two-sided round: group coverage rows on the left
and normalized residual-deletion rows on the right. -/
abbrev TwoSidedLowerRow (Group Job Slot : Type*) :=
  Group ⊕ ResidualDeleteRow Job Slot

/-- Coefficients of the combined lower-tail row family. -/
noncomputable def twoSidedLowerWeight
    (members : Group → Finset Job) (lambda : ℕ) :
    TwoSidedLowerRow Group Job Slot → Option → ℝ
  | Sum.inl g => H.jobGroupCoverageWeight members g
  | Sum.inr r => H.residualDeleteWeight lambda r

@[simp] theorem twoSidedLowerWeight_group
    (members : Group → Finset Job) (lambda : ℕ) (g : Group) (o : Option) :
    H.twoSidedLowerWeight members lambda (Sum.inl g) o =
      H.jobGroupCoverageWeight members g o := rfl

@[simp] theorem twoSidedLowerWeight_residual
    (members : Group → Finset Job) (lambda : ℕ)
    (r : ResidualDeleteRow Job Slot) (o : Option) :
    H.twoSidedLowerWeight members lambda (Sum.inr r) o =
      H.residualDeleteWeight lambda r o := rfl

@[simp] theorem linearRowSupport_twoSidedLowerWeight_group
    (members : Group → Finset Job) (lambda : ℕ) (g : Group) :
    linearRowSupport (H.twoSidedLowerWeight members lambda) (Sum.inl g) =
      linearRowSupport (H.jobGroupCoverageWeight members) g := rfl

@[simp] theorem linearRowSupport_twoSidedLowerWeight_residual
    (members : Group → Finset Job) (lambda : ℕ)
    (r : ResidualDeleteRow Job Slot) :
    linearRowSupport (H.twoSidedLowerWeight members lambda) (Sum.inr r) =
      linearRowSupport (H.residualDeleteWeight lambda) r := rfl

@[simp] theorem linearRowMean_twoSidedLowerWeight_group
    (q : Option → ℝ) (members : Group → Finset Job) (lambda : ℕ)
    (g : Group) :
    linearRowMean q (H.twoSidedLowerWeight members lambda) (Sum.inl g) =
      linearRowMean q (H.jobGroupCoverageWeight members) g := rfl

@[simp] theorem linearRowMean_twoSidedLowerWeight_residual
    (q : Option → ℝ) (members : Group → Finset Job) (lambda : ℕ)
    (r : ResidualDeleteRow Job Slot) :
    linearRowMean q (H.twoSidedLowerWeight members lambda) (Sum.inr r) =
      linearRowMean q (H.residualDeleteWeight lambda) r := rfl

theorem twoSidedLowerWeight_nonneg
    (members : Group → Finset Job) (lambda : ℕ) :
    ∀ r o, 0 ≤ H.twoSidedLowerWeight members lambda r o := by
  intro r o
  rcases r with g | r
  · exact H.jobGroupCoverageWeight_nonneg members g o
  · exact H.residualDeleteWeight_nonneg lambda r o

theorem twoSidedLowerWeight_le_one
    (members : Group → Finset Job) (lambda : ℕ) (hlambda : 0 < lambda)
    (hjobSlot : ∀ j s, H.jobSlotCodegree j s ≤ lambda)
    (hslotPair : ∀ s t, s ≠ t → H.slotPairCodegree s t ≤ lambda) :
    ∀ r o, H.twoSidedLowerWeight members lambda r o ≤ 1 := by
  intro r o
  rcases r with g | r
  · exact H.jobGroupCoverageWeight_le_one members g o
  · exact H.residualDeleteWeight_le_one lambda hlambda hjobSlot hslotPair r o

/-- Incidence in the disjoint sum is the sum of the two incidences. -/
theorem linearRowIncidence_twoSidedLowerWeight_card
    (members : Group → Finset Job) (lambda : ℕ) (o : Option) :
    (linearRowIncidence (H.twoSidedLowerWeight members lambda) o).card =
      (linearRowIncidence (H.jobGroupCoverageWeight members) o).card +
        (linearRowIncidence (H.residualDeleteWeight lambda) o).card := by
  classical
  have hset :
      linearRowIncidence (H.twoSidedLowerWeight members lambda) o =
        (linearRowIncidence (H.jobGroupCoverageWeight members) o).disjSum
          (linearRowIncidence (H.residualDeleteWeight lambda) o) := by
    ext r
    rcases r with g | r
    · simp [linearRowIncidence]
    · simp [linearRowIncidence]
  rw [hset, Finset.card_disjSum]

/-- An option belongs to at most `R + 8D` combined lower-tail rows. -/
theorem twoSidedLowerWeight_incidence_card_le
    (members : Group → Finset Job) (lambda D R : ℕ)
    (hjobDegree : ∀ j, (H.fiber j).card ≤ D)
    (hslotDegree : ∀ s, H.slotDegree s ≤ D)
    (hgroupIncidence : ∀ j,
      ((Finset.univ : Finset Group).filter
        (fun g ↦ j ∈ members g)).card ≤ R)
    (o : Option) :
    (linearRowIncidence (H.twoSidedLowerWeight members lambda) o).card ≤
      R + 8 * D := by
  rw [H.linearRowIncidence_twoSidedLowerWeight_card members lambda o]
  exact Nat.add_le_add
    (H.jobGroupCoverage_incidence_card_le members R hgroupIncidence o)
    (H.residualDeleteWeight_incidence_card_le_eight_mul
      lambda D hjobDegree hslotDegree o)

/-- Normalized lower deletion bounds imply genuine degree shrink.  The factor
two is the exact loss in passing from blocker multiplicity to the number of
distinct removed options. -/
theorem genuine_degree_shrink_of_normalized_delete_lower
    (lambda : ℕ) (hlambda : 0 < lambda) (S : Finset Option)
    (hS : H.IsPartialMatching S)
    (lowerJobBudget : Job → ℕ) (lowerSlotBudget : Slot → ℕ)
    (hjob : ∀ j, ¬ H.Covers S j →
      (lowerJobBudget j : ℝ) / (2 * lambda : ℕ) <
        H.externalJobDeletionLoad S j / (2 * lambda : ℕ))
    (hslot : ∀ s, (∀ p ∈ S, s ∉ H.slots p) →
      (lowerSlotBudget s : ℝ) / (3 * lambda : ℕ) <
        H.slotDeletionLoad S s / (3 * lambda : ℕ)) :
    (∀ j, ¬ H.Covers S j →
      2 * H.residualJobDegree S j + lowerJobBudget j ≤
        2 * H.residualJobDegree ∅ j) ∧
    (∀ s, (∀ p ∈ S, s ∉ H.slots p) →
      2 * H.residualSlotDegree S s + lowerSlotBudget s ≤
        2 * H.residualSlotDegree ∅ s) := by
  constructor
  · intro j huncovered
    have hden : (0 : ℝ) < (2 * lambda : ℕ) := by positivity
    have hcast : (lowerJobBudget j : ℝ) <
        H.externalJobDeletionLoad S j := by
      exact (div_lt_div_iff_of_pos_right hden).mp (hjob j huncovered)
    have hnat : lowerJobBudget j ≤ H.externalJobDeletionLoad S j := by
      have : lowerJobBudget j < H.externalJobDeletionLoad S j := by
        exact_mod_cast hcast
      omega
    exact H.two_mul_residualJobDegree_add_linearLower_le
      S j hS huncovered (lowerJobBudget j) hnat
  · intro s hunused
    have hden : (0 : ℝ) < (3 * lambda : ℕ) := by positivity
    have hcast : (lowerSlotBudget s : ℝ) <
        H.slotDeletionLoad S s := by
      exact (div_lt_div_iff_of_pos_right hden).mp (hslot s hunused)
    have hnat : lowerSlotBudget s ≤ H.slotDeletionLoad S s := by
      have : lowerSlotBudget s < H.slotDeletionLoad S s := by
        exact_mod_cast hcast
      omega
    exact H.two_mul_residualSlotDegree_add_linearLower_le
      S s hS hunused (lowerSlotBudget s) hnat

/-- One exact two-sided Harris round.  The lower deletion thresholds are
normalized: job rows use denominator `2*lambda`, and unused-slot rows use
denominator `3*lambda`.  The conclusion is conditional on the displayed
conflict bound and exponential bounds for group coverage and residual
deletion. -/
theorem exists_oneRound_residual_harris_two_sided
    (q : Option → ℝ) (members : Group → Finset Job)
    (lambda : ℕ) (hlambda : 0 < lambda)
    (groupThreshold groupLambda : Group → ℝ)
    (lowerDeleteThreshold lowerDeleteLambda :
      ResidualDeleteRow Job Slot → ℝ)
    (jobBudget : Job → ℕ) (slotBudget : Slot → ℕ)
    (upperLambda : ResidualDeleteRow Job Slot → ℝ)
    (D R : ℕ) (pairX rowX cap : ℝ)
    (hq0 : ∀ o, 0 ≤ q o) (hq1 : ∀ o, q o ≤ 1)
    (hjobDegree : ∀ j, (H.fiber j).card ≤ D)
    (hslotDegree : ∀ s, H.slotDegree s ≤ D)
    (hjobSlot : ∀ j s, H.jobSlotCodegree j s ≤ lambda)
    (hslotPair : ∀ s t, s ≠ t → H.slotPairCodegree s t ≤ lambda)
    (hgroupIncidence : ∀ j,
      ((Finset.univ : Finset Group).filter
        (fun g ↦ j ∈ members g)).card ≤ R)
    (hgroupLambda : ∀ g, 0 ≤ groupLambda g)
    (hlowerDeleteLambda : ∀ r, 0 ≤ lowerDeleteLambda r)
    (hupperLambda : ∀ r, 0 ≤ upperLambda r)
    (hpairX0 : 0 ≤ pairX) (hrowX0 : 0 ≤ rowX)
    (hpairXcap : pairX ≤ cap) (hrowXcap : rowX ≤ cap)
    (hcap1 : cap < 1)
    (hpair : ∀ c : H.ConflictIndex,
      q (H.canonicalConflictLeft c) * q (H.canonicalConflictRight c) ≤
        pairX * (1 - rowX) ^ (2 * (R + 8 * D)))
    (hgroupLower : ∀ g,
      Real.exp (groupLambda g * groupThreshold g +
          (Real.exp (-groupLambda g) - 1) *
            linearRowMean q (H.jobGroupCoverageWeight members) g) ≤
        rowX * (1 - cap) ^
          ((linearRowSupport
            (H.jobGroupCoverageWeight members) g).card * (14 * D)))
    (hdeleteLower : ∀ r,
      Real.exp (lowerDeleteLambda r * lowerDeleteThreshold r +
          (Real.exp (-lowerDeleteLambda r) - 1) *
            linearRowMean q (H.residualDeleteWeight lambda) r) ≤
        rowX * (1 - cap) ^
          ((linearRowSupport
            (H.residualDeleteWeight lambda) r).card * (14 * D)))
    (hdeleteUpper : ∀ r,
      Real.exp (-upperLambda r *
          residualDeleteThreshold lambda jobBudget slotBudget r +
        (Real.exp (upperLambda r) - 1) *
          linearRowMean q (H.residualDeleteWeight lambda) r) ≤
        rowX * (1 - rowX) ^
          ((linearRowSupport (H.residualDeleteWeight lambda) r).card *
            (R + 8 * D))) :
    ∃ S : Finset Option,
      H.IsPartialMatching S ∧
      (∀ g, groupThreshold g <
        (H.coveredGroupJobs members g S).card) ∧
      (∀ j, ¬ H.Covers S j →
        lowerDeleteThreshold (Sum.inl j) <
          H.externalJobDeletionLoad S j / (2 * lambda : ℕ)) ∧
      (∀ s, (∀ p ∈ S, s ∉ H.slots p) →
        lowerDeleteThreshold (Sum.inr s) <
          H.slotDeletionLoad S s / (3 * lambda : ℕ)) ∧
      (∀ j, ¬ H.Covers S j →
        H.residualJobDegree ∅ j ≤ H.residualJobDegree S j + jobBudget j) ∧
      (∀ s, (∀ p ∈ S, s ∉ H.slots p) →
        H.residualSlotDegree ∅ s ≤
          H.residualSlotDegree S s + slotBudget s) := by
  let lowerThreshold : TwoSidedLowerRow Group Job Slot → ℝ
    | Sum.inl g => groupThreshold g
    | Sum.inr r => lowerDeleteThreshold r
  let lowerLambda : TwoSidedLowerRow Group Job Slot → ℝ
    | Sum.inl g => groupLambda g
    | Sum.inr r => lowerDeleteLambda r
  have hlowerLambda : ∀ r, 0 ≤ lowerLambda r := by
    intro r
    rcases r with g | r
    · exact hgroupLambda g
    · exact hlowerDeleteLambda r
  have hlowerIncidence : ∀ o,
      (linearRowIncidence (H.twoSidedLowerWeight members lambda) o).card ≤
        R + 8 * D := by
    exact H.twoSidedLowerWeight_incidence_card_le members lambda D R
      hjobDegree hslotDegree hgroupIncidence
  have hlowerNumeric : ∀ r,
      Real.exp (lowerLambda r * lowerThreshold r +
        (Real.exp (-lowerLambda r) - 1) *
          linearRowMean q (H.twoSidedLowerWeight members lambda) r) ≤
        rowX * (1 - cap) ^
          ((linearRowSupport (H.twoSidedLowerWeight members lambda) r).card *
            (6 * D + 8 * D)) := by
    have hsum : 6 * D + 8 * D = 14 * D := by omega
    intro r
    rcases r with g | r
    · simpa [lowerLambda, lowerThreshold, hsum] using hgroupLower g
    · simpa [lowerLambda, lowerThreshold, hsum] using hdeleteLower r
  rcases H.exists_partialMatching_with_lower_and_upper_rows_harris_of_incidence
      H.canonicalConflictLeft H.canonicalConflictRight q
      (H.twoSidedLowerWeight members lambda)
      (H.residualDeleteWeight lambda) lowerThreshold lowerLambda
      (residualDeleteThreshold lambda jobBudget slotBudget) upperLambda
      H.canonicalConflict_ne H.canonicalConflict_complete
      (6 * D) (R + 8 * D) (8 * D) pairX rowX cap
      hq0 hq1
      (H.twoSidedLowerWeight_nonneg members lambda)
      (H.twoSidedLowerWeight_le_one members lambda hlambda hjobSlot hslotPair)
      (H.residualDeleteWeight_nonneg lambda)
      (H.residualDeleteWeight_le_one lambda hlambda hjobSlot hslotPair)
      hlowerLambda hupperLambda hpairX0 hrowX0 hpairXcap hrowXcap hcap1
      (H.canonicalConflict_incidence_card_le_six_mul
        D hjobDegree hslotDegree)
      hlowerIncidence
      (H.residualDeleteWeight_incidence_card_le_eight_mul
        lambda D hjobDegree hslotDegree)
      hpair hlowerNumeric hdeleteUpper with
    ⟨S, hS, hlower, hupper⟩
  have hgroup : ∀ g, groupThreshold g <
      (H.coveredGroupJobs members g S).card := by
    intro g
    apply H.coveredGroupJobs_count_gt_of_row_gt members g S hS
    have h := hlower (Sum.inl g)
    rw [weightedSum_linearRowSupport
      (H.twoSidedLowerWeight members lambda) (Sum.inl g) S] at h
    simpa [lowerThreshold, twoSidedLowerWeight] using h
  have hjobLower : ∀ j, ¬ H.Covers S j →
      lowerDeleteThreshold (Sum.inl j) <
        H.externalJobDeletionLoad S j / (2 * lambda : ℕ) := by
    intro j _huncovered
    have h := hlower (Sum.inr (Sum.inl j))
    rw [weightedSum_linearRowSupport
      (H.twoSidedLowerWeight members lambda) (Sum.inr (Sum.inl j)) S] at h
    change lowerDeleteThreshold (Sum.inl j) <
      ∑ o ∈ S, H.residualDeleteWeight lambda (Sum.inl j) o at h
    rw [H.selected_residualDeleteWeight_job lambda S j] at h
    exact h
  have hslotLower : ∀ s, (∀ p ∈ S, s ∉ H.slots p) →
      lowerDeleteThreshold (Sum.inr s) <
        H.slotDeletionLoad S s / (3 * lambda : ℕ) := by
    intro s hunused
    have h := hlower (Sum.inr (Sum.inr s))
    rw [weightedSum_linearRowSupport
      (H.twoSidedLowerWeight members lambda) (Sum.inr (Sum.inr s)) S] at h
    change lowerDeleteThreshold (Sum.inr s) <
      ∑ o ∈ S, H.residualDeleteWeight lambda (Sum.inr s) o at h
    rw [H.selected_residualDeleteWeight_slot lambda S s hunused] at h
    exact h
  have hjobUpper : ∀ j, ¬ H.Covers S j →
      H.residualJobDegree ∅ j ≤ H.residualJobDegree S j + jobBudget j := by
    intro j huncovered
    have hnorm := hupper (Sum.inl j)
    rw [weightedSum_linearRowSupport
      (H.residualDeleteWeight lambda) (Sum.inl j) S] at hnorm
    rw [H.selected_residualDeleteWeight_job lambda S j] at hnorm
    have hden : (0 : ℝ) < (2 * lambda : ℕ) := by positivity
    have hcast : (H.externalJobDeletionLoad S j : ℝ) < jobBudget j := by
      apply (div_lt_div_iff_of_pos_right hden).mp
      simpa [residualDeleteThreshold] using hnorm
    have hload : H.externalJobDeletionLoad S j < jobBudget j := by
      exact_mod_cast hcast
    have hremoved :=
      H.removedResidualFiber_empty_card_le_externalJobDeletionLoad
        S j huncovered
    have hidentity := H.residualJobDegree_union_add_removed ∅ S j
    simp only [Finset.empty_union] at hidentity
    omega
  have hslotUpper : ∀ s, (∀ p ∈ S, s ∉ H.slots p) →
      H.residualSlotDegree ∅ s ≤
        H.residualSlotDegree S s + slotBudget s := by
    intro s hunused
    have hnorm := hupper (Sum.inr s)
    rw [weightedSum_linearRowSupport
      (H.residualDeleteWeight lambda) (Sum.inr s) S] at hnorm
    rw [H.selected_residualDeleteWeight_slot lambda S s hunused] at hnorm
    have hden : (0 : ℝ) < (3 * lambda : ℕ) := by positivity
    have hcast : (H.slotDeletionLoad S s : ℝ) < slotBudget s := by
      apply (div_lt_div_iff_of_pos_right hden).mp
      simpa [residualDeleteThreshold] using hnorm
    have hload : H.slotDeletionLoad S s < slotBudget s := by
      exact_mod_cast hcast
    have hremoved :=
      H.removedResidualSlot_empty_card_le_slotDeletionLoad S s hunused
    have hidentity := H.residualSlotDegree_union_add_removed ∅ S s
    simp only [Finset.empty_union] at hidentity
    omega
  exact ⟨S, hS, hgroup, hjobLower, hslotLower, hjobUpper, hslotUpper⟩

/-- Natural-budget form of the two-sided round.  Its lower rows now give a
direct decrease of every surviving residual job and slot degree, while the
upper rows prevent excessive decrease in the same round. -/
theorem exists_oneRound_residual_harris_two_sided_degree_bounds
    (q : Option → ℝ) (members : Group → Finset Job)
    (lambda : ℕ) (hlambda : 0 < lambda)
    (groupThreshold groupLambda : Group → ℝ)
    (lowerJobBudget : Job → ℕ) (lowerSlotBudget : Slot → ℕ)
    (lowerDeleteLambda : ResidualDeleteRow Job Slot → ℝ)
    (upperJobBudget : Job → ℕ) (upperSlotBudget : Slot → ℕ)
    (upperLambda : ResidualDeleteRow Job Slot → ℝ)
    (D R : ℕ) (pairX rowX cap : ℝ)
    (hq0 : ∀ o, 0 ≤ q o) (hq1 : ∀ o, q o ≤ 1)
    (hjobDegree : ∀ j, (H.fiber j).card ≤ D)
    (hslotDegree : ∀ s, H.slotDegree s ≤ D)
    (hjobSlot : ∀ j s, H.jobSlotCodegree j s ≤ lambda)
    (hslotPair : ∀ s t, s ≠ t → H.slotPairCodegree s t ≤ lambda)
    (hgroupIncidence : ∀ j,
      ((Finset.univ : Finset Group).filter
        (fun g ↦ j ∈ members g)).card ≤ R)
    (hgroupLambda : ∀ g, 0 ≤ groupLambda g)
    (hlowerDeleteLambda : ∀ r, 0 ≤ lowerDeleteLambda r)
    (hupperLambda : ∀ r, 0 ≤ upperLambda r)
    (hpairX0 : 0 ≤ pairX) (hrowX0 : 0 ≤ rowX)
    (hpairXcap : pairX ≤ cap) (hrowXcap : rowX ≤ cap)
    (hcap1 : cap < 1)
    (hpair : ∀ c : H.ConflictIndex,
      q (H.canonicalConflictLeft c) * q (H.canonicalConflictRight c) ≤
        pairX * (1 - rowX) ^ (2 * (R + 8 * D)))
    (hgroupLower : ∀ g,
      Real.exp (groupLambda g * groupThreshold g +
          (Real.exp (-groupLambda g) - 1) *
            linearRowMean q (H.jobGroupCoverageWeight members) g) ≤
        rowX * (1 - cap) ^
          ((linearRowSupport
            (H.jobGroupCoverageWeight members) g).card * (14 * D)))
    (hdeleteLower : ∀ r,
      Real.exp (lowerDeleteLambda r *
          residualDeleteThreshold lambda lowerJobBudget lowerSlotBudget r +
        (Real.exp (-lowerDeleteLambda r) - 1) *
          linearRowMean q (H.residualDeleteWeight lambda) r) ≤
        rowX * (1 - cap) ^
          ((linearRowSupport
            (H.residualDeleteWeight lambda) r).card * (14 * D)))
    (hdeleteUpper : ∀ r,
      Real.exp (-upperLambda r *
          residualDeleteThreshold lambda upperJobBudget upperSlotBudget r +
        (Real.exp (upperLambda r) - 1) *
          linearRowMean q (H.residualDeleteWeight lambda) r) ≤
        rowX * (1 - rowX) ^
          ((linearRowSupport (H.residualDeleteWeight lambda) r).card *
            (R + 8 * D))) :
    ∃ S : Finset Option,
      H.IsPartialMatching S ∧
      (∀ g, groupThreshold g <
        (H.coveredGroupJobs members g S).card) ∧
      (∀ j, ¬ H.Covers S j →
        2 * H.residualJobDegree S j + lowerJobBudget j ≤
          2 * H.residualJobDegree ∅ j) ∧
      (∀ s, (∀ p ∈ S, s ∉ H.slots p) →
        2 * H.residualSlotDegree S s + lowerSlotBudget s ≤
          2 * H.residualSlotDegree ∅ s) ∧
      (∀ j, ¬ H.Covers S j →
        H.residualJobDegree ∅ j ≤
          H.residualJobDegree S j + upperJobBudget j) ∧
      (∀ s, (∀ p ∈ S, s ∉ H.slots p) →
        H.residualSlotDegree ∅ s ≤
          H.residualSlotDegree S s + upperSlotBudget s) := by
  rcases H.exists_oneRound_residual_harris_two_sided
      q members lambda hlambda groupThreshold groupLambda
      (residualDeleteThreshold lambda lowerJobBudget lowerSlotBudget)
      lowerDeleteLambda upperJobBudget upperSlotBudget upperLambda
      D R pairX rowX cap hq0 hq1 hjobDegree hslotDegree hjobSlot hslotPair
      hgroupIncidence hgroupLambda hlowerDeleteLambda hupperLambda
      hpairX0 hrowX0 hpairXcap hrowXcap hcap1
      hpair hgroupLower hdeleteLower hdeleteUpper with
    ⟨S, hS, hgroup, hjobLower, hslotLower, hjobUpper, hslotUpper⟩
  have hshrink := H.genuine_degree_shrink_of_normalized_delete_lower
    lambda hlambda S hS lowerJobBudget lowerSlotBudget
  have hjobNormalized : ∀ j, ¬ H.Covers S j →
      (lowerJobBudget j : ℝ) / (2 * lambda : ℕ) <
        H.externalJobDeletionLoad S j / (2 * lambda : ℕ) := by
    intro j huncovered
    simpa [residualDeleteThreshold] using hjobLower j huncovered
  have hslotNormalized : ∀ s, (∀ p ∈ S, s ∉ H.slots p) →
      (lowerSlotBudget s : ℝ) / (3 * lambda : ℕ) <
        H.slotDeletionLoad S s / (3 * lambda : ℕ) := by
    intro s hunused
    simpa [residualDeleteThreshold] using hslotLower s hunused
  rcases hshrink hjobNormalized hslotNormalized with
    ⟨hjobShrink, hslotShrink⟩
  exact ⟨S, hS, hgroup, hjobShrink, hslotShrink,
    hjobUpper, hslotUpper⟩

end WeightedEdgeColoring.RankThreeOptionSystem
