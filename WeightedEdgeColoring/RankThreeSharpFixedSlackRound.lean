import WeightedEdgeColoring.RankThreeDirectNibbleHarrisExtra
import WeightedEdgeColoring.RankThreeResidualActiveSlotUniform
import WeightedEdgeColoring.RankThreeCollisionSupport
import WeightedEdgeColoring.RankThreeCollisionTail
import WeightedEdgeColoring.RankThreeFixedSlackRoundBridge
import WeightedEdgeColoring.RankThreeFixedSlackGapPreservation

/-!
# One sharp fixed-slack rank-three round

This module combines canonical conflict events, lower slot-deletion rows,
upper job-deletion rows, and quadratic slot-collision events in one Harris
local-lemma round.  Every slot is declared active by using `ActiveSlot 0`.
The thresholds are exactly those required by
`fixedSlack_balance_of_jobLoss_slotLoad_collision`.
-/

namespace WeightedEdgeColoring.RankThreeOptionSystem

open scoped BigOperators
open WeightedEdgeColoring.FiniteBernoulliChernoff
open WeightedEdgeColoring.FiniteBernoulliSupportSplit

universe u v w x

variable {Job : Type u} {Slot : Type v} {Option : Type w} {Group : Type x}
  [Fintype Job] [Fintype Slot] [Fintype Option] [Fintype Group]
  [DecidableEq Job] [DecidableEq Slot] [DecidableEq Option] [DecidableEq Group]
  (H : RankThreeOptionSystem Job Slot Option)

/-- Lower thresholds for group coverage and the sharp slot load. -/
noncomputable def sharpFixedSlackLowerThreshold
    (groupThreshold : Group → ℝ) (lambda d : ℕ)
    (a gamma etaLoad : ℝ) :
    H.ActiveSlotLowerRow (Group := Group) 0 → ℝ
  | Sum.inl g => groupThreshold g
  | Sum.inr _ =>
      (a * (2 - gamma) * (1 - gamma) - etaLoad) * d /
        (3 * lambda : ℕ)

/-- Chernoff parameters for the two lower-row kinds. -/
noncomputable def sharpFixedSlackLowerLambda
    (groupLambda : Group → ℝ) (slotLambda : Slot → ℝ) :
    H.ActiveSlotLowerRow (Group := Group) 0 → ℝ
  | Sum.inl g => groupLambda g
  | Sum.inr s => slotLambda s.1

/-- Normalized upper threshold which gives the exact fixed-slack job-loss
budget after multiplying by `2*lambda`. -/
noncomputable def sharpFixedSlackJobThreshold
    (lambda d : ℕ) (a gamma etaJob : ℝ) (_j : Job) : ℝ :=
  (2 * a * (1 - gamma) + etaJob) * d / (2 * lambda : ℕ)

/-- Exact scalar separation with three independent error budgets. -/
theorem sharpFixedSlack_separated_exact_gap
    (a gamma etaJob etaLoad etaCollision : ℝ) :
    (1 - gamma) * (WeightedEdgeColoring.fixedSlackJobRetention a gamma - etaJob) -
      (WeightedEdgeColoring.fixedSlackSlotRetention a gamma * (1 - gamma) +
        etaLoad + etaCollision) =
      a * gamma * (1 - gamma) -
        ((1 - gamma) * etaJob + etaLoad + etaCollision) := by
  simp only [WeightedEdgeColoring.fixedSlackJobRetention, WeightedEdgeColoring.fixedSlackSlotRetention]
  ring

theorem sharpFixedSlack_preserves_same_gap_separated
    (a gamma etaJob etaLoad etaCollision : ℝ)
    (herror : (1 - gamma) * etaJob + etaLoad + etaCollision ≤
      a * gamma * (1 - gamma)) :
    WeightedEdgeColoring.fixedSlackSlotRetention a gamma * (1 - gamma) +
        etaLoad + etaCollision ≤
      (1 - gamma) *
        (WeightedEdgeColoring.fixedSlackJobRetention a gamma - etaJob) := by
  apply sub_nonneg.mp
  rw [sharpFixedSlack_separated_exact_gap]
  linarith

/-- Numerical recurrence form: the output bounds of one sharp round retain
the same slot/job gap. -/
theorem sharpFixedSlack_output_preserves_same_gap
    (d : ℕ) (a gamma etaJob etaLoad etaCollision jobNext slotNext : ℝ)
    (hgamma1 : gamma ≤ 1)
    (herror : (1 - gamma) * etaJob + etaLoad + etaCollision ≤
      a * gamma * (1 - gamma))
    (hjob : (WeightedEdgeColoring.fixedSlackJobRetention a gamma - etaJob) * d ≤
      jobNext)
    (hslot : slotNext ≤
      (WeightedEdgeColoring.fixedSlackSlotRetention a gamma * (1 - gamma) +
        etaLoad + etaCollision) * d) :
    slotNext ≤ (1 - gamma) * jobNext := by
  have hfactor : 0 ≤ 1 - gamma := by linarith
  have hscalar := sharpFixedSlack_preserves_same_gap_separated
    a gamma etaJob etaLoad etaCollision herror
  calc
    slotNext ≤
        (WeightedEdgeColoring.fixedSlackSlotRetention a gamma * (1 - gamma) +
          etaLoad + etaCollision) * d := hslot
    _ ≤ (1 - gamma) *
        (WeightedEdgeColoring.fixedSlackJobRetention a gamma - etaJob) * d := by
      exact mul_le_mul_of_nonneg_right hscalar (Nat.cast_nonneg d)
    _ ≤ (1 - gamma) * jobNext := by
      rw [mul_assoc]
      exact mul_le_mul_of_nonneg_left hjob hfactor

/-- Deterministic fixed-slack bridge with independent job, slot-load, and
collision errors. -/
theorem separatedFixedSlack_balance
    (A : Finset Option) (d : ℕ)
    (a gamma etaJob etaLoad etaCollision : ℝ)
    (hjobInitial : ∀ j, d ≤ H.residualJobDegree ∅ j)
    (hjobLoss : ∀ j, ¬ H.Covers A j →
      ((H.removedResidualFiber ∅ A j).card : ℝ) ≤
        (2 * a * (1 - gamma) + etaJob) * d)
    (hslotInitial : ∀ s,
      (H.residualSlotDegree ∅ s : ℝ) ≤ (1 - gamma) * d)
    (hslotLoad : ∀ s, (∀ p ∈ A, s ∉ H.slots p) →
      (a * (2 - gamma) * (1 - gamma) - etaLoad) * d ≤
        (H.slotDeletionLoad A s : ℝ))
    (hslotCollision : ∀ s, (∀ p ∈ A, s ∉ H.slots p) →
      (WeightedEdgeColoring.collisionDeficit A (H.slotBlockedBy s) : ℝ) ≤
        etaCollision * d) :
    (∀ j, ¬ H.Covers A j →
      (WeightedEdgeColoring.fixedSlackJobRetention a gamma - etaJob) * d ≤
        H.residualJobDegree A j) ∧
    (∀ s, (∀ p ∈ A, s ∉ H.slots p) →
      (H.residualSlotDegree A s : ℝ) ≤
        (WeightedEdgeColoring.fixedSlackSlotRetention a gamma * (1 - gamma) +
          etaLoad + etaCollision) * d) := by
  constructor
  · intro j huncovered
    have hid := H.residualJobDegree_union_add_removed ∅ A j
    simp only [Finset.empty_union] at hid
    have hidReal :
        (H.residualJobDegree A j : ℝ) +
            (H.removedResidualFiber ∅ A j).card =
          H.residualJobDegree ∅ j := by exact_mod_cast hid
    have hinitial : (d : ℝ) ≤ H.residualJobDegree ∅ j := by
      exact_mod_cast hjobInitial j
    have hloss := hjobLoss j huncovered
    rw [WeightedEdgeColoring.fixedSlackJobRetention]
    push_cast
    nlinarith
  · intro s hunused
    have hdelete := H.slotDeletionLoad_eq_removed_add_collisionDeficit
      A s hunused
    have hdeleteReal :
        (H.slotDeletionLoad A s : ℝ) =
          (H.removedResidualSlot ∅ A s).card +
            WeightedEdgeColoring.collisionDeficit A (H.slotBlockedBy s) := by
      exact_mod_cast hdelete
    have hid := H.residualSlotDegree_union_add_removed ∅ A s
    simp only [Finset.empty_union] at hid
    have hidReal :
        (H.residualSlotDegree A s : ℝ) +
            (H.removedResidualSlot ∅ A s).card =
          H.residualSlotDegree ∅ s := by exact_mod_cast hid
    have hinitial := hslotInitial s
    have hload := hslotLoad s hunused
    have hcollision := hslotCollision s hunused
    rw [WeightedEdgeColoring.fixedSlackSlotRetention]
    push_cast
    nlinarith

/-- The elementary quadratic-moment tail discharges the collision-event LLL
hypothesis once its envelope fits below the collision budget. -/
theorem sharpFixedSlack_collisionNumeric_of_moment
    (q : Option → ℝ) (qmax lowerX : ℝ) (collisionX : Slot → ℝ)
    (lambda d D R k : ℕ) (etaCollision : ℝ)
    (hq0 : ∀ o, 0 ≤ q o) (hq1 : ∀ o, q o ≤ 1)
    (hqmax0 : 0 ≤ qmax) (hqmax : ∀ o, q o ≤ qmax)
    (hjobDegree : ∀ j, (H.fiber j).card ≤ D)
    (hslotDegree : ∀ s, H.slotDegree s ≤ D)
    (hjobSlot : ∀ j s, H.jobSlotCodegree j s ≤ lambda)
    (hslotPair : ∀ s t, s ≠ t → H.slotPairCodegree s t ≤ lambda)
    (hT : 0 < 2 * etaCollision * d)
    (henvelope : slotCollisionMomentEnvelope qmax D D lambda k ≤
      etaCollision * d)
    (hhalfProduct : ∀ s,
      (1 / 2 : ℝ) ^ k ≤ collisionX s * (1 - lowerX) ^
        ((H.slotCollisionSupport s).card * (R + 8 * D))) :
    ∀ s,
      WeightedEdgeColoring.FiniteLocalLemma.eventMass
          (bernoulliMass (insideParameter q (H.slotCollisionSupport s)))
          (H.slotCollisionLocalBad s (2 * etaCollision * d)) ≤
        collisionX s * (1 - lowerX) ^
          ((H.slotCollisionSupport s).card * (R + 8 * D)) := by
  intro s
  apply (H.slotCollisionLocalBad_mass_le_half_pow
    q qmax s D D lambda k (2 * etaCollision * d)
    hq0 hq1 hqmax0 hqmax hjobDegree hslotDegree hjobSlot hslotPair hT ?_).trans
    (hhalfProduct s)
  nlinarith

/-- The concrete one-round theorem.  The four displayed numerical
hypotheses are precisely the pair, lower-row, upper-row, and collision-event
LLL inequalities. -/
theorem exists_sharpFixedSlackRound_harris_extra
    (q : Option → ℝ) (members : Group → Finset Job)
    (groupThreshold groupLambda : Group → ℝ)
    (slotLambda : Slot → ℝ) (jobLambda : Job → ℝ)
    (lambda d D R : ℕ)
    (a gamma etaJob etaLoad etaCollision : ℝ)
    (pairX lowerX upperX cap : ℝ) (collisionX : Slot → ℝ)
    (hlambda : 0 < lambda)
    (hq0 : ∀ o, 0 ≤ q o) (hq1 : ∀ o, q o ≤ 1)
    (hjobInitial : ∀ j, d ≤ H.residualJobDegree ∅ j)
    (hslotInitial : ∀ s,
      (H.residualSlotDegree ∅ s : ℝ) ≤ (1 - gamma) * d)
    (hjobDegree : ∀ j, (H.fiber j).card ≤ D)
    (hslotDegree : ∀ s, H.slotDegree s ≤ D)
    (hjobSlot : ∀ j s, H.jobSlotCodegree j s ≤ lambda)
    (hslotPair : ∀ s t, s ≠ t → H.slotPairCodegree s t ≤ lambda)
    (hgroupIncidence : ∀ j,
      ((Finset.univ : Finset Group).filter
        (fun g ↦ j ∈ members g)).card ≤ R)
    (hgroupLambda : ∀ g, 0 ≤ groupLambda g)
    (hslotLambda : ∀ s, 0 ≤ slotLambda s)
    (hjobLambda : ∀ j, 0 ≤ jobLambda j)
    (hpairX0 : 0 ≤ pairX) (hlowerX0 : 0 ≤ lowerX)
    (hupperX0 : 0 ≤ upperX) (hcollisionX0 : ∀ s, 0 ≤ collisionX s)
    (hpairXcap : pairX ≤ cap) (hupperXcap : upperX ≤ cap)
    (hcollisionXcap : ∀ s, collisionX s ≤ cap)
    (hlowerX1 : lowerX < 1) (hcap1 : cap < 1)
    (hpairNumeric : ∀ c : H.ConflictIndex,
      q (H.canonicalConflictLeft c) * q (H.canonicalConflictRight c) ≤
        pairX * (1 - lowerX) ^ (2 * (R + 8 * D)))
    (hgroupLowerNumeric : ∀ g,
      Real.exp (groupLambda g * groupThreshold g +
          (Real.exp (-groupLambda g) - 1) *
            linearRowMean q (H.jobGroupCoverageWeight members) g) ≤
        lowerX * (1 - cap) ^
          ((linearRowSupport
            (H.jobGroupCoverageWeight members) g).card * (16 * D)))
    (hslotLowerNumeric : ∀ s : H.ActiveSlot 0,
      Real.exp (slotLambda s.1 *
          ((a * (2 - gamma) * (1 - gamma) - etaLoad) * d /
            (3 * lambda : ℕ)) +
          (Real.exp (-slotLambda s.1) - 1) *
            linearRowMean q (H.residualDeleteWeight lambda) (Sum.inr s.1)) ≤
        lowerX * (1 - cap) ^
          ((linearRowSupport (H.residualDeleteWeight lambda)
            (Sum.inr s.1)).card * (16 * D)))
    (hjobUpperNumeric : ∀ j,
      Real.exp (-jobLambda j *
          ((2 * a * (1 - gamma) + etaJob) * d /
            (2 * lambda : ℕ)) +
          (Real.exp (jobLambda j) - 1) *
            linearRowMean q (H.residualDeleteWeight lambda) (Sum.inl j)) ≤
        upperX * (1 - lowerX) ^
          ((linearRowSupport (H.residualDeleteWeight lambda)
            (Sum.inl j)).card * (R + 8 * D)))
    (hcollisionNumeric : ∀ s,
      WeightedEdgeColoring.FiniteLocalLemma.eventMass
          (bernoulliMass (insideParameter q (H.slotCollisionSupport s)))
          (H.slotCollisionLocalBad s (2 * etaCollision * d)) ≤
        collisionX s * (1 - lowerX) ^
          ((H.slotCollisionSupport s).card * (R + 8 * D))) :
    ∃ A : Finset Option,
      H.IsPartialMatching A ∧
      (∀ g, groupThreshold g <
        ∑ o ∈ A, H.jobGroupCoverageWeight members g o) ∧
      (∀ j, ¬ H.Covers A j →
        (WeightedEdgeColoring.fixedSlackJobRetention a gamma - etaJob) * d ≤
          H.residualJobDegree A j) ∧
      (∀ s, (∀ p ∈ A, s ∉ H.slots p) →
        (H.residualSlotDegree A s : ℝ) ≤
          (WeightedEdgeColoring.fixedSlackSlotRetention a gamma * (1 - gamma) +
            etaLoad + etaCollision) * d) := by
  let lowerWeight := H.activeSlotLowerWeight members lambda 0
  let upperWeight := H.residualJobUpperWeight lambda
  let lowerThreshold := H.sharpFixedSlackLowerThreshold
    groupThreshold lambda d a gamma etaLoad
  let lowerLambda := H.sharpFixedSlackLowerLambda groupLambda slotLambda
  let upperThreshold : Job → ℝ := sharpFixedSlackJobThreshold
    lambda d a gamma etaJob
  have hlowerLambda : ∀ r, 0 ≤ lowerLambda r := by
    intro r
    rcases r with g | s
    · exact hgroupLambda g
    · exact hslotLambda s.1
  have hlowerNumeric : ∀ r,
      Real.exp (lowerLambda r * lowerThreshold r +
          (Real.exp (-lowerLambda r) - 1) * linearRowMean q lowerWeight r) ≤
        lowerX * (1 - cap) ^
          ((linearRowSupport lowerWeight r).card *
            ((6 * D) + (2 * D) + (8 * D))) := by
    have hsum : (6 * D) + (2 * D) + (8 * D) = 16 * D := by omega
    intro r
    rcases r with g | s
    · simpa [lowerWeight, lowerThreshold, lowerLambda,
        sharpFixedSlackLowerThreshold, sharpFixedSlackLowerLambda, hsum] using
        hgroupLowerNumeric g
    · simpa [lowerWeight, lowerThreshold, lowerLambda,
        sharpFixedSlackLowerThreshold, sharpFixedSlackLowerLambda, hsum] using
        hslotLowerNumeric s
  have hupperNumeric : ∀ j,
      Real.exp (-jobLambda j * upperThreshold j +
          (Real.exp (jobLambda j) - 1) * linearRowMean q upperWeight j) ≤
        upperX * (1 - lowerX) ^
          ((linearRowSupport upperWeight j).card * (R + 8 * D)) := by
    intro j
    simpa [upperWeight, upperThreshold, sharpFixedSlackJobThreshold] using
      hjobUpperNumeric j
  rcases H.exists_partialMatching_with_extra_increasing_harris_of_incidence
      H.canonicalConflictLeft H.canonicalConflictRight q
      lowerWeight upperWeight lowerThreshold lowerLambda upperThreshold jobLambda
      H.canonicalConflict_ne H.canonicalConflict_complete
      H.slotCollisionSupport
      (fun s ↦ H.slotCollisionLocalBad s (2 * etaCollision * d))
      (fun s ↦ H.slotCollisionLocalBad_isIncreasing s
        (2 * etaCollision * d))
      (6 * D) (R + 8 * D) (2 * D) (8 * D)
      pairX lowerX upperX cap collisionX
      hq0 hq1
      (H.activeSlotLowerWeight_nonneg members lambda 0)
      (H.activeSlotLowerWeight_le_one members lambda 0 hlambda
        hjobSlot hslotPair)
      (H.residualJobUpperWeight_nonneg lambda)
      (H.residualJobUpperWeight_le_one lambda hlambda hjobSlot hslotPair)
      hlowerLambda hjobLambda hpairX0 hlowerX0 hupperX0 hcollisionX0
      hpairXcap hupperXcap hcollisionXcap hlowerX1 hcap1
      (H.canonicalConflict_incidence_card_le_six_mul
        D hjobDegree hslotDegree)
      (H.activeSlotLowerWeight_incidence_card_le
        members lambda 0 D R hjobDegree hslotDegree hgroupIncidence)
      (H.residualJobUpperWeight_incidence_card_le_slot lambda D hslotDegree)
      (H.slotCollisionIncidence_card_le_eight_mul
        lambda D hlambda hjobDegree hslotDegree)
      hpairNumeric hlowerNumeric hupperNumeric hcollisionNumeric with
    ⟨A, hmatching, hlower, hupper, hextra⟩
  have hgroup : ∀ g, groupThreshold g <
      ∑ o ∈ A, H.jobGroupCoverageWeight members g o := by
    intro g
    have h := hlower (Sum.inl g)
    rw [weightedSum_linearRowSupport lowerWeight (Sum.inl g) A] at h
    simpa [lowerWeight, lowerThreshold, sharpFixedSlackLowerThreshold] using h
  have hjobLoss : ∀ j, ¬ H.Covers A j →
      ((H.removedResidualFiber ∅ A j).card : ℝ) ≤
        (2 * a * (1 - gamma) + etaJob) * d := by
    intro j huncovered
    have h := hupper j
    rw [weightedSum_linearRowSupport upperWeight j A] at h
    change (∑ o ∈ A, H.residualDeleteWeight lambda (Sum.inl j) o) <
      (2 * a * (1 - gamma) + etaJob) * d / (2 * lambda : ℕ) at h
    rw [H.selected_residualDeleteWeight_job lambda A j] at h
    have hden : (0 : ℝ) < (2 * lambda : ℕ) := by positivity
    have hload : (H.externalJobDeletionLoad A j : ℝ) <
        (2 * a * (1 - gamma) + etaJob) * d := by
      exact (div_lt_div_iff_of_pos_right hden).mp h
    have hremoved :=
      H.removedResidualFiber_empty_card_le_externalJobDeletionLoad
        A j huncovered
    have hremovedR : ((H.removedResidualFiber ∅ A j).card : ℝ) ≤
        H.externalJobDeletionLoad A j := by
      exact_mod_cast hremoved
    exact hremovedR.trans hload.le
  have hslotLoad : ∀ s, (∀ p ∈ A, s ∉ H.slots p) →
      (a * (2 - gamma) * (1 - gamma) - etaLoad) * d ≤
        (H.slotDeletionLoad A s : ℝ) := by
    intro s hunused
    let active : H.ActiveSlot 0 := ⟨s, Nat.zero_le _⟩
    have h := hlower (Sum.inr active)
    rw [weightedSum_linearRowSupport lowerWeight (Sum.inr active) A] at h
    change (a * (2 - gamma) * (1 - gamma) - etaLoad) * d /
        (3 * lambda : ℕ) <
      ∑ o ∈ A, H.residualDeleteWeight lambda (Sum.inr s) o at h
    rw [H.selected_residualDeleteWeight_slot lambda A s hunused] at h
    have hden : (0 : ℝ) < (3 * lambda : ℕ) := by positivity
    exact ((div_lt_div_iff_of_pos_right hden).mp h).le
  have hslotCollision : ∀ s, (∀ p ∈ A, s ∉ H.slots p) →
      (WeightedEdgeColoring.collisionDeficit A (H.slotBlockedBy s) : ℝ) ≤
        etaCollision * d := by
    intro s hunused
    have hlocalNot := hextra s
    have hglobalNot : A ∉ upperTail
        (fun B : Finset Option ↦
          (pairCollisionStatistic (H.avoidingSlotBlockedBy s) B : ℝ))
        (2 * etaCollision * d) := by
      rw [← H.insideCylinder_slotCollisionLocalBad s
        (2 * etaCollision * d)]
      simpa only [mem_insideCylinder] using hlocalNot
    have hpairAvoid :
        (pairCollisionStatistic (H.avoidingSlotBlockedBy s) A : ℝ) <
          2 * etaCollision * d := by
      exact lt_of_not_ge (fun hge ↦ hglobalNot
        (Finset.mem_filter.mpr ⟨Finset.mem_univ A, hge⟩))
    have htwo := two_mul_collisionDeficit_le_pairCollisionStatistic
      A (H.avoidingSlotBlockedBy s)
    have htwoReal :
        (2 : ℝ) * collisionDeficit A (H.avoidingSlotBlockedBy s) ≤
          pairCollisionStatistic (H.avoidingSlotBlockedBy s) A := by
      exact_mod_cast htwo
    rw [H.collisionDeficit_avoidingSlotBlockedBy_eq A s hunused] at htwoReal
    nlinarith
  have hbalance := H.separatedFixedSlack_balance
    A d a gamma etaJob etaLoad etaCollision hjobInitial hjobLoss
      hslotInitial hslotLoad hslotCollision
  exact ⟨A, hmatching, hgroup, hbalance.1, hbalance.2⟩

end WeightedEdgeColoring.RankThreeOptionSystem
