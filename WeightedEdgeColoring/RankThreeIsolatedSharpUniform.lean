import WeightedEdgeColoring.RankThreeIsolatedSharpFixedSlackRound
import WeightedEdgeColoring.RankThreeSharpFixedSlackNumeric

/-!
# Uniform isolated sharp round

This is the graph-bookkeeping wrapper for the raw-sample-then-isolate
round.  There are no pair-conflict events.  Endpoint and slot lower rows
each receive an explicit isolation-loss allowance; the same logarithmic
moment order controls those losses and the usual slot-collision deficit.
-/

namespace WeightedEdgeColoring.RankThreeOptionSystem

open scoped BigOperators
open WeightedEdgeColoring.FiniteBernoulliChernoff
open WeightedEdgeColoring.SharpFixedSlackNumeric

universe u v w x

variable {Job : Type u} {Slot : Type v} {Option : Type w} {Group : Type x}
  [Fintype Job] [Fintype Slot] [Fintype Option] [Fintype Group]
  [DecidableEq Job] [DecidableEq Slot] [DecidableEq Option] [DecidableEq Group]
  (H : RankThreeOptionSystem Job Slot Option)

/-- Neighbor exponent of a lower row in the isolated architecture. -/
def isolatedLowerNeighborBudget (support R D : ℕ) : ℕ :=
  support * (2 * D + ((3 * D + 1) * (R + 8 * D) + 8 * D))

/-- Enlarging a support by every conflict neighbor costs at most `3D+1`. -/
def isolatedConflictSupportBudget (support D : ℕ) : ℕ :=
  support * (3 * D + 1)

/-- Uniform proposal specialization of the isolated sharp round.

The hypotheses after the degree assumptions are ordinary scalar
inequalities.  In particular, all actual support sizes, row means, event
incidences, and local event masses have been eliminated. -/
theorem exists_isolatedSharpFixedSlackRound_uniformProposal
    (members : Group → Finset Job)
    (slotLambda : Slot → ℝ) (jobLambda : Job → ℝ)
    (lambda d D R K m k : ℕ)
    (rho a gamma etaJob etaLoad etaIsolation etaCollision z delta : ℝ)
    (hlambda : 0 < lambda)
    (hrho0 : 0 ≤ rho) (hrho1 : rho ≤ 1)
    (hrho : rho = a / (d : ℝ))
    (hjobInitial : ∀ j, d ≤ H.residualJobDegree ∅ j)
    (hslotInitial : ∀ s,
      (H.residualSlotDegree ∅ s : ℝ) ≤ (1 - gamma) * d)
    (hjobDegree : ∀ j, (H.fiber j).card ≤ D)
    (hslotDegree : ∀ s, H.slotDegree s ≤ D)
    (hjobSlot : ∀ j s, H.jobSlotCodegree j s ≤ lambda)
    (hslotPair : ∀ s t, s ≠ t → H.slotPairCodegree s t ≤ lambda)
    (hmembers : ∀ g, (members g).card ≤ K)
    (hgroupSupportLower : ∀ g,
      m ≤ (linearRowSupport
        (H.jobGroupCoverageWeight members) g).card)
    (hgroupIncidence : ∀ j,
      ((Finset.univ : Finset Group).filter
        (fun g ↦ j ∈ members g)).card ≤ R)
    (hdeltaPos : 0 < delta) (hdelta1 : delta ≤ 1)
    (hrhoPos : 0 < rho) (hmPos : 0 < m)
    (hetaIsolation : 0 < etaIsolation)
    (hslotLambda : ∀ s, 0 ≤ slotLambda s)
    (hjobLambda : ∀ j, 0 ≤ jobLambda j)
    (hz : 0 < z)
    (hrowHalf : exponentialRowWeight z ≤ 1 / 2)
    (hcollisionRow : collisionWeight k ≤ exponentialRowWeight z)
    (hgroupExponent :
      Real.exp
          (((delta / 2) * (1 - delta / 2) +
              (Real.exp (-(delta / 2)) - 1)) * (rho * (m : ℝ))) ≤
        Real.exp (-(z + 2 * exponentialRowWeight z *
          (isolatedLowerNeighborBudget (groupSupportBudget K D) R D : ℝ))))
    (hslotExponent : ∀ s : H.ActiveSlot 0,
      Real.exp (slotLambda s.1 *
          (((a * (2 - gamma) * (1 - gamma) - etaLoad) * d /
              (3 * lambda : ℕ)) + etaIsolation * d / (3 * lambda : ℕ)) +
        (Real.exp (-slotLambda s.1) - 1) *
          linearRowMean (fun _ : Option ↦ rho)
            (H.residualDeleteWeight lambda) (Sum.inr s.1)) ≤
        Real.exp (-(z + 2 * exponentialRowWeight z *
          (isolatedLowerNeighborBudget (slotSupportBudget D) R D : ℝ))))
    (hupperTail : ∀ j,
      Real.exp (-jobLambda j *
          ((2 * a * (1 - gamma) + etaJob) * d /
            (2 * lambda : ℕ)) +
        (Real.exp (jobLambda j) - 1) *
          linearRowMean (fun _ : Option ↦ rho)
            (H.residualDeleteWeight lambda) (Sum.inl j)) ≤
        exponentialRowWeight z / 2)
    (hupperProduct : exponentialRowWeight z *
      (increasingNeighborBudget (upperSupportBudget D) R D : ℝ) ≤ 1 / 2)
    (hgroupLossEnvelope :
      isolatedRowConflictWeightedMomentEnvelope rho (K * D) (3 * D) k ≤
        ((delta / 2) * rho * m) / 2)
    (hslotLossEnvelope :
      isolatedRowConflictWeightedMomentEnvelope rho
          ((D : ℝ) ^ 2 / lambda) (3 * D) k ≤
        (etaIsolation * d / (3 * lambda : ℕ)) / 2)
    (hgroupLossProduct : exponentialRowWeight z *
      (increasingNeighborBudget
        (isolatedConflictSupportBudget (groupSupportBudget K D) D) R D : ℝ) ≤
        1 / 2)
    (hslotLossProduct : exponentialRowWeight z *
      (increasingNeighborBudget
        (isolatedConflictSupportBudget (slotSupportBudget D) D) R D : ℝ) ≤
        1 / 2)
    (hcollisionThreshold : 0 < 2 * etaCollision * d)
    (hcollisionEnvelope :
      slotCollisionMomentEnvelope rho D D lambda k ≤ etaCollision * d)
    (hcollisionProduct : exponentialRowWeight z *
      (increasingNeighborBudget (slotSupportBudget D) R D : ℝ) ≤ 1 / 2) :
    ∃ A : Finset Option,
      H.IsPartialMatching A ∧
      (∀ g, (1 - delta) * (a / (d : ℝ)) * m <
        ∑ o ∈ A, H.jobGroupCoverageWeight members g o) ∧
      (∀ j, ¬ H.Covers A j →
        (WeightedEdgeColoring.fixedSlackJobRetention a gamma - etaJob) * d ≤
          H.residualJobDegree A j) ∧
      (∀ s, (∀ p ∈ A, s ∉ H.slots p) →
        (H.residualSlotDegree A s : ℝ) ≤
          (WeightedEdgeColoring.fixedSlackSlotRetention a gamma * (1 - gamma) +
            etaLoad + etaCollision) * d) := by
  let lowerX := exponentialRowWeight z
  let cap := lowerX
  let lossThreshold := H.isolatedSharpLossThreshold
    (Group := Group) (fun _ ↦ (delta / 2) * rho * m)
      etaIsolation lambda d
  let lossWeightSum := H.isolatedSharpLossWeightSum
    (Group := Group) K D lambda
  let lossX : H.IsolatedSharpLowerRow (Group := Group) → ℝ :=
    fun _ ↦ collisionWeight k
  let collisionX : Slot → ℝ := fun _ ↦ collisionWeight k
  have hlowerX0 : 0 ≤ lowerX := exponentialRowWeight_nonneg z
  have hlowerX1 : lowerX < 1 := by
    exact Real.exp_lt_one_iff.mpr (neg_lt_zero.mpr hz)
  have hcap0 : 0 ≤ cap := hlowerX0
  have hcapHalf : cap ≤ 1 / 2 := by simpa [cap, lowerX] using hrowHalf
  have hcap1 : cap < 1 := hcapHalf.trans_lt (by norm_num)
  have hd : 0 < d := by
    by_contra hnot
    have hd0 : d = 0 := Nat.eq_zero_of_not_pos hnot
    subst d
    norm_num at hrho
    linarith
  have hlossThreshold : ∀ r, 0 < lossThreshold r := by
    intro r
    rcases r with g | s
    · dsimp [lossThreshold, isolatedSharpLossThreshold]
      positivity
    · dsimp [lossThreshold, isolatedSharpLossThreshold]
      positivity
  have hlossWeightSum := H.activeSlotLowerWeight_sum_le_isolatedSharpLossWeightSum
    members lambda K D hlambda hmembers hjobDegree hslotDegree
  have hlossEnvelope : ∀ r,
      isolatedRowConflictWeightedMomentEnvelope rho (lossWeightSum r)
          (3 * D) k ≤ lossThreshold r / 2 := by
    intro r
    rcases r with g | s
    · simpa [lossWeightSum, lossThreshold, isolatedSharpLossWeightSum,
        isolatedSharpLossThreshold] using hgroupLossEnvelope
    · simpa [lossWeightSum, lossThreshold, isolatedSharpLossWeightSum,
        isolatedSharpLossThreshold] using hslotLossEnvelope
  have hlossProduct : ∀ r,
      (1 / 2 : ℝ) ^ k ≤ lossX r * (1 - lowerX) ^
        ((H.isolatedRowConflictSupport
          (H.activeSlotLowerWeight members lambda 0) r).card * (R + 8 * D)) := by
    intro r
    apply collisionNumeric_of_half ((1 / 2 : ℝ) ^ k)
      (lossX r) lowerX
      ((H.isolatedRowConflictSupport
        (H.activeSlotLowerWeight members lambda 0) r).card * (R + 8 * D))
      (match r with
        | Sum.inl _ => isolatedConflictSupportBudget (groupSupportBudget K D) D
        | Sum.inr _ => isolatedConflictSupportBudget (slotSupportBudget D) D)
      R D
    · exact collisionWeight_nonneg k
    · exact hlowerX0
    · exact hlowerX1.le
    · rcases r with g | s
      · unfold increasingNeighborBudget isolatedConflictSupportBudget
        apply Nat.mul_le_mul_right (R + 8 * D)
        apply H.isolatedRowConflictSupport_card_le
        · exact H.jobGroupCoverage_support_card_le members K D
            hmembers hjobDegree g
        · exact H.conflictNeighbors_card_le_three_mul D
            hjobDegree hslotDegree
      · unfold increasingNeighborBudget isolatedConflictSupportBudget
        apply Nat.mul_le_mul_right (R + 8 * D)
        apply H.isolatedRowConflictSupport_card_le
        · exact H.activeSlot_support_card_le_job_slot lambda D D
            hjobDegree hslotDegree s.1
        · exact H.conflictNeighbors_card_le_three_mul D
            hjobDegree hslotDegree
    · simpa [lossX] using (half_pow_eq_collisionWeight_div_two k).le
    · rcases r with g | s
      · simpa [lowerX] using hgroupLossProduct
      · simpa [lowerX] using hslotLossProduct
  have hgroupLowerNumeric : ∀ g,
      Real.exp ((delta / 2) *
          ((1 - delta) * rho * m + (delta / 2) * rho * m) +
        (Real.exp (-(delta / 2)) - 1) *
          linearRowMean (fun _ : Option ↦ rho)
            (H.jobGroupCoverageWeight members) g) ≤
        lowerX * (1 - cap) ^
          ((linearRowSupport
            (H.jobGroupCoverageWeight members) g).card *
              (2 * D + ((3 * D + 1) * (R + 8 * D) + 8 * D))) := by
    intro g
    have hmean : rho * (m : ℝ) ≤
        linearRowMean (fun _ : Option ↦ rho)
          (H.jobGroupCoverageWeight members) g := by
      rw [H.linearRowMean_jobGroupCoverageWeight_uniform]
      apply mul_le_mul_of_nonneg_left _ hrho0
      exact_mod_cast hgroupSupportLower g
    have hcoef : Real.exp (-(delta / 2)) - 1 ≤ 0 := by
      apply sub_nonpos.mpr
      apply Real.exp_le_one_iff.mpr
      have : 0 ≤ delta / 2 := by positivity
      linarith
    have hfirst :
        Real.exp ((delta / 2) *
            ((1 - delta) * rho * m + (delta / 2) * rho * m) +
          (Real.exp (-(delta / 2)) - 1) *
            linearRowMean (fun _ : Option ↦ rho)
              (H.jobGroupCoverageWeight members) g) ≤
          Real.exp (((delta / 2) * (1 - delta / 2) +
              (Real.exp (-(delta / 2)) - 1)) * (rho * (m : ℝ))) := by
      apply Real.exp_le_exp.mpr
      calc
        (delta / 2) * ((1 - delta) * rho * m +
            (delta / 2) * rho * m) +
            (Real.exp (-(delta / 2)) - 1) *
              linearRowMean (fun _ : Option ↦ rho)
                (H.jobGroupCoverageWeight members) g ≤
          (delta / 2) * ((1 - delta) * rho * m +
            (delta / 2) * rho * m) +
            (Real.exp (-(delta / 2)) - 1) * (rho * m) :=
              by
                have hmul := mul_le_mul_of_nonpos_left hmean hcoef
                linarith
        _ = ((delta / 2) * (1 - delta / 2) +
              (Real.exp (-(delta / 2)) - 1)) * (rho * (m : ℝ)) := by ring
    apply tail_le_exp_mul_one_sub_pow_of_exp_budget _ z cap
      ((linearRowSupport (H.jobGroupCoverageWeight members) g).card *
        (2 * D + ((3 * D + 1) * (R + 8 * D) + 8 * D)))
      (isolatedLowerNeighborBudget (groupSupportBudget K D) R D)
      hcap0 hcapHalf
    · unfold isolatedLowerNeighborBudget
      exact Nat.mul_le_mul_right _
        (H.jobGroupCoverage_support_card_le members K D
          hmembers hjobDegree g)
    · simpa [lowerX, cap] using hfirst.trans hgroupExponent
  have hslotLowerNumeric : ∀ s : H.ActiveSlot 0,
      Real.exp (slotLambda s.1 *
          (((a * (2 - gamma) * (1 - gamma) - etaLoad) * d /
              (3 * lambda : ℕ)) + etaIsolation * d / (3 * lambda : ℕ)) +
        (Real.exp (-slotLambda s.1) - 1) *
          linearRowMean (fun _ : Option ↦ rho)
            (H.residualDeleteWeight lambda) (Sum.inr s.1)) ≤
        lowerX * (1 - cap) ^
          ((linearRowSupport (H.residualDeleteWeight lambda)
            (Sum.inr s.1)).card *
              (2 * D + ((3 * D + 1) * (R + 8 * D) + 8 * D))) := by
    intro s
    apply tail_le_exp_mul_one_sub_pow_of_exp_budget _ z cap
      ((linearRowSupport (H.residualDeleteWeight lambda) (Sum.inr s.1)).card *
        (2 * D + ((3 * D + 1) * (R + 8 * D) + 8 * D)))
      (isolatedLowerNeighborBudget (slotSupportBudget D) R D)
      hcap0 hcapHalf
    · unfold isolatedLowerNeighborBudget
      exact Nat.mul_le_mul_right _
        (H.activeSlot_support_card_le_job_slot lambda D D
          hjobDegree hslotDegree s.1)
    · simpa [lowerX, cap] using hslotExponent s
  have hupperNumeric : ∀ j,
      Real.exp (-jobLambda j *
          ((2 * a * (1 - gamma) + etaJob) * d /
            (2 * lambda : ℕ)) +
        (Real.exp (jobLambda j) - 1) *
          linearRowMean (fun _ : Option ↦ rho)
            (H.residualDeleteWeight lambda) (Sum.inl j)) ≤
        lowerX * (1 - lowerX) ^
          ((linearRowSupport (H.residualDeleteWeight lambda)
            (Sum.inl j)).card * (R + 8 * D)) := by
    intro j
    apply upperNumeric_of_half _ lowerX lowerX
      ((linearRowSupport (H.residualDeleteWeight lambda) (Sum.inl j)).card *
        (R + 8 * D)) (upperSupportBudget D) R D
      hlowerX0 hlowerX0 hlowerX1.le
    · unfold increasingNeighborBudget upperSupportBudget
      exact Nat.mul_le_mul_right _
        (H.residualJobUpper_support_card_le_job_slot
          lambda D D hjobDegree hslotDegree j)
    · simpa [lowerX] using hupperTail j
    · simpa [lowerX] using hupperProduct
  have hcollisionHalfProduct : ∀ s,
      (1 / 2 : ℝ) ^ k ≤ collisionX s * (1 - lowerX) ^
        ((H.slotCollisionSupport s).card * (R + 8 * D)) := by
    intro s
    apply collisionNumeric_of_half ((1 / 2 : ℝ) ^ k)
      (collisionX s) lowerX
      ((H.slotCollisionSupport s).card * (R + 8 * D))
      (slotSupportBudget D) R D
    · exact collisionWeight_nonneg k
    · exact hlowerX0
    · exact hlowerX1.le
    · unfold increasingNeighborBudget slotSupportBudget
      exact Nat.mul_le_mul_right _
        (H.slotCollisionSupport_card_le_job_slot
          lambda D D hlambda hjobDegree hslotDegree s)
    · simpa [collisionX] using (half_pow_eq_collisionWeight_div_two k).le
    · simpa [lowerX] using hcollisionProduct
  have hcollisionNumeric := H.sharpFixedSlack_collisionNumeric_of_moment
    (fun _ : Option ↦ rho) rho lowerX collisionX lambda d D R k
    etaCollision (fun _ ↦ hrho0) (fun _ ↦ hrho1) hrho0
    (fun _ ↦ le_rfl) hjobDegree hslotDegree hjobSlot hslotPair
    hcollisionThreshold hcollisionEnvelope hcollisionHalfProduct
  simpa [hrho] using H.exists_isolatedSharpFixedSlackRound
    (fun _ : Option ↦ rho) rho members
    (fun _ ↦ (1 - delta) * rho * m)
    (fun _ ↦ delta / 2) slotLambda jobLambda
    lossThreshold lossWeightSum lossX collisionX
    lambda d D R k a gamma etaJob etaLoad etaCollision
    lowerX lowerX cap hlambda (fun _ ↦ hrho0) (fun _ ↦ hrho1)
    hrho0 (fun _ ↦ le_rfl) hjobInitial hslotInitial
    hjobDegree hslotDegree hjobSlot hslotPair hgroupIncidence
    (fun _ ↦ by positivity) hslotLambda hjobLambda
    hlowerX0 hlowerX0 hcap0 (by simp [cap])
    (fun _ ↦ collisionWeight_nonneg k)
    (fun _ ↦ by simpa [lossX, cap, lowerX] using hcollisionRow)
    (fun _ ↦ collisionWeight_nonneg k)
    (fun _ ↦ by simpa [collisionX, cap, lowerX] using hcollisionRow)
    hlowerX1 hcap1 hlossThreshold hlossWeightSum hlossEnvelope
    hlossProduct hgroupLowerNumeric hslotLowerNumeric hupperNumeric
    hcollisionNumeric

end WeightedEdgeColoring.RankThreeOptionSystem
