import WeightedEdgeColoring.RankThreeSharpFixedSlackRound
import WeightedEdgeColoring.RankThreeSharpFixedSlackNumeric

/-!
# Uniform-proposal specialization of the sharp fixed-slack round

This module performs the graph bookkeeping and the four Harris product
comparisons.  The remaining hypotheses are scalar Chernoff exponent bounds,
the quadratic-moment envelope, and elementary comparisons between the four
chosen LLL weights.  Thus a later asymptotic module can substitute
`rho = a/d`, `a = alpha/lambda`, and its preferred choices of `z` and `k`
without reopening any incidence or support proof.
-/

namespace WeightedEdgeColoring.RankThreeOptionSystem

open scoped BigOperators
open WeightedEdgeColoring.FiniteBernoulliChernoff
open WeightedEdgeColoring.FiniteBernoulliSupportSplit
open WeightedEdgeColoring.SharpFixedSlackNumeric

universe u v w x

variable {Job : Type u} {Slot : Type v} {Option : Type w} {Group : Type x}
  [Fintype Job] [Fintype Slot] [Fintype Option] [Fintype Group]
  [DecidableEq Job] [DecidableEq Slot] [DecidableEq Option] [DecidableEq Group]
  (H : RankThreeOptionSystem Job Slot Option)

/-- Uniform sharp round with the intended four LLL weights.  Endpoint-block
groups have at most `K` jobs, at least `m` option coordinates, and each job
belongs to at most `R` groups. -/
theorem exists_sharpFixedSlackRound_uniformProposal
    (members : Group → Finset Job)
    (slotLambda : Slot → ℝ) (jobLambda : Job → ℝ)
    (lambda d D R K m k : ℕ)
    (rho a gamma etaJob etaLoad etaCollision z delta : ℝ)
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
    (hdelta0 : 0 ≤ delta)
    (hslotLambda : ∀ s, 0 ≤ slotLambda s)
    (hjobLambda : ∀ j, 0 ≤ jobLambda j)
    (hz : 0 < z)
    (hcapHalf : increasingCap rho ≤ 1 / 2)
    (hrowCap : exponentialRowWeight z ≤ increasingCap rho)
    (hcollisionCap : collisionWeight k ≤ increasingCap rho)
    (hpairProductCost :
      exponentialRowWeight z * (pairNeighborBudget R D : ℝ) ≤ 1 / 2)
    (hgroupExponent :
      Real.exp
          ((delta * (1 - delta) + (Real.exp (-delta) - 1)) *
            (rho * (m : ℝ))) ≤
        Real.exp (-(z + 2 * increasingCap rho *
          (lowerNeighborBudget (groupSupportBudget K D) D : ℝ))))
    (hslotExponent : ∀ s : H.ActiveSlot 0,
      Real.exp (slotLambda s.1 *
          ((a * (2 - gamma) * (1 - gamma) - etaLoad) * d /
            (3 * lambda : ℕ)) +
        (Real.exp (-slotLambda s.1) - 1) *
          linearRowMean (fun _ : Option ↦ rho)
            (H.residualDeleteWeight lambda) (Sum.inr s.1)) ≤
        Real.exp (-(z + 2 * increasingCap rho *
          (lowerNeighborBudget (slotSupportBudget D) D : ℝ))))
    (hupperTail : ∀ j,
      Real.exp (-jobLambda j *
          ((2 * a * (1 - gamma) + etaJob) * d /
            (2 * lambda : ℕ)) +
        (Real.exp (jobLambda j) - 1) *
          linearRowMean (fun _ : Option ↦ rho)
            (H.residualDeleteWeight lambda) (Sum.inl j)) ≤
        exponentialRowWeight z / 2)
    (hupperProductCost : exponentialRowWeight z *
      (increasingNeighborBudget (upperSupportBudget D) R D : ℝ) ≤ 1 / 2)
    (hcollisionThreshold : 0 < 2 * etaCollision * d)
    (hcollisionEnvelope :
      slotCollisionMomentEnvelope rho D D lambda k ≤ etaCollision * d)
    (hcollisionProductCost : exponentialRowWeight z *
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
  let pairX := pairWeight rho
  let cap := increasingCap rho
  let collisionX : Slot → ℝ := fun _ ↦ collisionWeight k
  have hlowerX0 : 0 ≤ lowerX := exponentialRowWeight_nonneg z
  have hlowerX1 : lowerX < 1 := by
    dsimp [lowerX, exponentialRowWeight]
    exact Real.exp_lt_one_iff.mpr (neg_lt_zero.mpr hz)
  have hcap0 : 0 ≤ cap := increasingCap_nonneg rho
  have hcap1 : cap < 1 := hcapHalf.trans_lt (by norm_num)
  have hgroupLowerNumeric : ∀ g,
      Real.exp (delta * ((1 - delta) * rho * m) +
          (Real.exp (-delta) - 1) *
            linearRowMean (fun _ : Option ↦ rho)
              (H.jobGroupCoverageWeight members) g) ≤
        lowerX * (1 - cap) ^
          ((linearRowSupport
            (H.jobGroupCoverageWeight members) g).card * (16 * D)) := by
    intro g
    have hmean : rho * (m : ℝ) ≤
        linearRowMean (fun _ : Option ↦ rho)
          (H.jobGroupCoverageWeight members) g := by
      rw [H.linearRowMean_jobGroupCoverageWeight_uniform]
      apply mul_le_mul_of_nonneg_left _ hrho0
      exact_mod_cast hgroupSupportLower g
    have hcoef : Real.exp (-delta) - 1 ≤ 0 := by
      apply sub_nonpos.mpr
      exact Real.exp_le_one_iff.mpr (neg_nonpos.mpr hdelta0)
    have hfirst :
        Real.exp (delta * ((1 - delta) * rho * m) +
            (Real.exp (-delta) - 1) *
              linearRowMean (fun _ : Option ↦ rho)
                (H.jobGroupCoverageWeight members) g) ≤
          Real.exp
            ((delta * (1 - delta) + (Real.exp (-delta) - 1)) *
              (rho * (m : ℝ))) := by
      apply Real.exp_le_exp.mpr
      calc
        delta * ((1 - delta) * rho * m) +
            (Real.exp (-delta) - 1) *
              linearRowMean (fun _ : Option ↦ rho)
                (H.jobGroupCoverageWeight members) g ≤
          delta * ((1 - delta) * rho * m) +
            (Real.exp (-delta) - 1) * (rho * m) :=
              by
                have hmul := mul_le_mul_of_nonpos_left hmean hcoef
                linarith
        _ = (delta * (1 - delta) + (Real.exp (-delta) - 1)) *
            (rho * (m : ℝ)) := by ring
    have htail := hfirst.trans hgroupExponent
    apply lowerNumeric_of_exp_budget
      _ z cap
      ((linearRowSupport
        (H.jobGroupCoverageWeight members) g).card * (16 * D))
      (groupSupportBudget K D) D hcap0 hcapHalf
    · unfold lowerNeighborBudget groupSupportBudget
      exact Nat.mul_le_mul_right (16 * D)
        (H.jobGroupCoverage_support_card_le members K D
          hmembers hjobDegree g)
    · simpa [lowerX, cap] using htail
  have hslotLowerNumeric : ∀ s : H.ActiveSlot 0,
      Real.exp (slotLambda s.1 *
          ((a * (2 - gamma) * (1 - gamma) - etaLoad) * d /
            (3 * lambda : ℕ)) +
        (Real.exp (-slotLambda s.1) - 1) *
          linearRowMean (fun _ : Option ↦ rho)
            (H.residualDeleteWeight lambda) (Sum.inr s.1)) ≤
        lowerX * (1 - cap) ^
          ((linearRowSupport (H.residualDeleteWeight lambda)
            (Sum.inr s.1)).card * (16 * D)) := by
    intro s
    apply lowerNumeric_of_exp_budget
      _ z cap
      ((linearRowSupport (H.residualDeleteWeight lambda)
        (Sum.inr s.1)).card * (16 * D))
      (slotSupportBudget D) D hcap0 hcapHalf
    · unfold lowerNeighborBudget slotSupportBudget
      exact Nat.mul_le_mul_right (16 * D)
        (H.activeSlot_support_card_le_job_slot
          lambda D D hjobDegree hslotDegree s.1)
    · simpa [lowerX, cap] using hslotExponent s
  have hpairNumeric : ∀ c : H.ConflictIndex,
      rho * rho ≤ pairX * (1 - lowerX) ^ (2 * (R + 8 * D)) := by
    intro c
    apply pairNumeric_of_half (rho * rho) pairX lowerX
      (2 * (R + 8 * D)) R D
    · exact pairWeight_nonneg rho
    · exact hlowerX0
    · exact hlowerX1.le
    · simp [pairNeighborBudget]
    · simpa [pairX, pow_two] using (sq_eq_pairWeight_div_two rho).le
    · simpa [lowerX] using hpairProductCost
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
      ((linearRowSupport (H.residualDeleteWeight lambda)
        (Sum.inl j)).card * (R + 8 * D))
      (upperSupportBudget D) R D hlowerX0 hlowerX0 hlowerX1.le
    · unfold increasingNeighborBudget upperSupportBudget
      exact Nat.mul_le_mul_right (R + 8 * D)
        (H.residualJobUpper_support_card_le_job_slot
          lambda D D hjobDegree hslotDegree j)
    · simpa [lowerX] using hupperTail j
    · simpa [lowerX] using hupperProductCost
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
      exact Nat.mul_le_mul_right (R + 8 * D)
        (H.slotCollisionSupport_card_le_job_slot
          lambda D D hlambda hjobDegree hslotDegree s)
    · simpa [collisionX] using (half_pow_eq_collisionWeight_div_two k).le
    · simpa [lowerX] using hcollisionProductCost
  have hcollisionNumeric := H.sharpFixedSlack_collisionNumeric_of_moment
    (fun _ : Option ↦ rho) rho lowerX collisionX lambda d D R k
    etaCollision (fun _ ↦ hrho0) (fun _ ↦ hrho1) hrho0 (fun _ ↦ le_rfl)
    hjobDegree hslotDegree hjobSlot hslotPair hcollisionThreshold
    hcollisionEnvelope hcollisionHalfProduct
  simpa [hrho] using H.exists_sharpFixedSlackRound_harris_extra
    (fun _ : Option ↦ rho) members
    (fun _ ↦ (1 - delta) * rho * m) (fun _ ↦ delta)
    slotLambda jobLambda lambda d D R a gamma etaJob etaLoad etaCollision
    pairX lowerX lowerX cap collisionX hlambda
    (fun _ ↦ hrho0) (fun _ ↦ hrho1) hjobInitial hslotInitial
    hjobDegree hslotDegree hjobSlot hslotPair hgroupIncidence
    (fun _ ↦ hdelta0) hslotLambda hjobLambda
    (pairWeight_nonneg rho) hlowerX0 hlowerX0
    (fun _ ↦ collisionWeight_nonneg k)
    (pairWeight_le_increasingCap rho) hrowCap
    (fun _ ↦ hcollisionCap) hlowerX1 hcap1
    hpairNumeric hgroupLowerNumeric hslotLowerNumeric hupperNumeric
    hcollisionNumeric

end WeightedEdgeColoring.RankThreeOptionSystem
