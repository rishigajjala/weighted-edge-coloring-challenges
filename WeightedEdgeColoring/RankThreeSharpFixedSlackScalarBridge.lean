import WeightedEdgeColoring.RankThreeOriginalTypeSharpStep
import WeightedEdgeColoring.RankThreeRegularSlotLowerIncidence
import WeightedEdgeColoring.RankThreeResidualDegreeMean

/-!
# Scalar bridge for the sharp fixed-slack round

After cyclic regularization, every job has degree `d` and every slot has
degree `S`.  The lower slot-deletion mean and the upper job-deletion mean
can therefore be replaced by two explicit scalar expressions.  This file
performs that replacement once.  A later asymptotic argument only has to
check inequalities between real numbers; it does not have to inspect the
regularized option system again.
-/

namespace WeightedEdgeColoring.RankThreeOptionSystem

open scoped BigOperators
open WeightedEdgeColoring.FiniteBernoulliChernoff
open WeightedEdgeColoring.SharpFixedSlackNumeric

universe u v w x

variable {Job : Type u} {Slot : Type v} {Option : Type w}
  [Fintype Job] [Fintype Slot] [Fintype Option]
  [DecidableEq Job] [DecidableEq Slot] [DecidableEq Option]
  {Group : Type x} [Fintype Group] [DecidableEq Group]

namespace OriginalIterationState.UniformSharpScalarData

/-- Build the scalar-data package for an exactly regular option system from
the two worst-case Chernoff exponents.  The slot expression uses the sharp
regular lower mean `rho*S*(d+S-3*lambda)/(3*lambda)`.  The job expression
uses the upper mean `rho*d*S/lambda`.

All local-lemma product comparisons remain scalar hypotheses.  In
particular, this theorem introduces no asymptotic or probabilistic premise
hidden behind a named proposition. -/
noncomputable def ofRegularBounds
    (H : RankThreeOptionSystem Job Slot Option)
    (members : Group → Finset Job)
    (lambda d S R K m k : ℕ)
    (rho a gamma etaJob etaLoad etaCollision z delta : ℝ)
    (slotTilt jobTilt : ℝ)
    (hlambda : 0 < lambda)
    (hrho0 : 0 ≤ rho) (hrho1 : rho ≤ 1)
    (hrho : rho = a / (d : ℝ))
    (htwo : ∀ o, (H.slots o).card = 2)
    (hjob : ∀ j, (H.fiber j).card = d)
    (hslot : ∀ s, H.slotDegree s = S)
    (hjobSlot : ∀ j s, H.jobSlotCodegree j s ≤ lambda)
    (hslotPair : ∀ s t, s ≠ t → H.slotPairCodegree s t ≤ lambda)
    (hdelta0 : 0 ≤ delta)
    (hslotTilt0 : 0 ≤ slotTilt) (hjobTilt0 : 0 ≤ jobTilt)
    (hz : 0 < z)
    (hcapHalf : increasingCap rho ≤ 1 / 2)
    (hrowCap : exponentialRowWeight z ≤ increasingCap rho)
    (hcollisionCap : collisionWeight k ≤ increasingCap rho)
    (hpairProduct : exponentialRowWeight z *
      (pairNeighborBudget R d : ℝ) ≤ 1 / 2)
    (hgroupExponent :
      Real.exp
          ((delta * (1 - delta) + (Real.exp (-delta) - 1)) *
            (rho * (m : ℝ))) ≤
        Real.exp (-(z + 2 * increasingCap rho *
          (lowerNeighborBudget (groupSupportBudget K d) d : ℝ))))
    (hslotExponent :
      Real.exp (slotTilt *
          ((a * (2 - gamma) * (1 - gamma) - etaLoad) * d /
            (3 * lambda : ℕ)) +
        (Real.exp (-slotTilt) - 1) *
          (rho * (((S * (d + S - 3 * lambda) : ℕ) : ℝ) /
            ((3 * lambda : ℕ) : ℝ)))) ≤
        Real.exp (-(z + 2 * increasingCap rho *
          (lowerNeighborBudget (slotSupportBudget d) d : ℝ))))
    (hupperExponent :
      Real.exp (-jobTilt *
          ((2 * a * (1 - gamma) + etaJob) * d /
            (2 * lambda : ℕ)) +
        (Real.exp jobTilt - 1) *
          (rho * ((d : ℝ) * (S : ℝ) / (lambda : ℝ)))) ≤
        exponentialRowWeight z / 2)
    (hupperProduct : exponentialRowWeight z *
      (increasingNeighborBudget (upperSupportBudget d) R d : ℝ) ≤ 1 / 2)
    (hcollisionThreshold : 0 < 2 * etaCollision * d)
    (hcollisionEnvelope :
      slotCollisionMomentEnvelope rho d d lambda k ≤ etaCollision * d)
    (hcollisionProduct : exponentialRowWeight z *
      (increasingNeighborBudget (slotSupportBudget d) R d : ℝ) ≤ 1 / 2) :
    OriginalIterationState.UniformSharpScalarData
      H members lambda d d R K m k
      rho a gamma etaJob etaLoad etaCollision z delta := by
  let slotLambda : Slot → ℝ := fun _ ↦ slotTilt
  let jobLambda : Job → ℝ := fun _ ↦ jobTilt
  refine
    { slotLambda := slotLambda
      jobLambda := jobLambda
      rho_nonneg := hrho0
      rho_le_one := hrho1
      rho_eq := hrho
      delta_nonneg := hdelta0
      slotLambda_nonneg := fun _ ↦ hslotTilt0
      jobLambda_nonneg := fun _ ↦ hjobTilt0
      z_pos := hz
      cap_le_half := hcapHalf
      row_le_cap := hrowCap
      collision_le_cap := hcollisionCap
      pair_product := hpairProduct
      group_exponent := hgroupExponent
      slot_exponent := ?_
      upper_tail := ?_
      upper_product := hupperProduct
      collision_threshold_pos := hcollisionThreshold
      collision_envelope := hcollisionEnvelope
      collision_product := hcollisionProduct }
  · intro s
    dsimp [slotLambda]
    have hmean := H.residualDeleteWeight_slot_mean_ge_regular
      rho s.1 d S lambda hlambda hrho0 htwo hjob hslot hjobSlot hslotPair
    have hcoef : Real.exp (-slotTilt) - 1 ≤ 0 := by
      exact sub_nonpos.mpr
        (Real.exp_le_one_iff.mpr (neg_nonpos.mpr hslotTilt0))
    have hreplace :
        (Real.exp (-slotTilt) - 1) *
            linearRowMean (fun _ : Option ↦ rho)
              (H.residualDeleteWeight lambda) (Sum.inr s.1) ≤
          (Real.exp (-slotTilt) - 1) *
            (rho * (((S * (d + S - 3 * lambda) : ℕ) : ℝ) /
              ((3 * lambda : ℕ) : ℝ))) :=
      mul_le_mul_of_nonpos_left hmean hcoef
    apply (Real.exp_le_exp.mpr ?_).trans hslotExponent
    linarith
  · intro j
    dsimp [jobLambda]
    have hslotLe : ∀ s, H.slotDegree s ≤ S := by
      intro s
      rw [hslot s]
    have hmean := H.residualDeleteWeight_job_mean_le_degree
      rho lambda S hlambda hrho0 j hslotLe
    have hjobCard : ((H.fiber j).card : ℝ) = d := by
      exact_mod_cast hjob j
    rw [hjobCard] at hmean
    have hcoef : 0 ≤ Real.exp jobTilt - 1 := by
      exact sub_nonneg.mpr (Real.one_le_exp hjobTilt0)
    have hreplace :
        (Real.exp jobTilt - 1) *
            linearRowMean (fun _ : Option ↦ rho)
              (H.residualDeleteWeight lambda) (Sum.inl j) ≤
          (Real.exp jobTilt - 1) *
            (rho * ((d : ℝ) * (S : ℝ) / (lambda : ℝ))) :=
      mul_le_mul_of_nonneg_left hmean hcoef
    apply (Real.exp_le_exp.mpr ?_).trans hupperExponent
    linarith

end OriginalIterationState.UniformSharpScalarData

end WeightedEdgeColoring.RankThreeOptionSystem
