import WeightedEdgeColoring.RankThreeSharpConcreteConstants
import WeightedEdgeColoring.RankThreeSharpFixedSlackScalarBridge
import WeightedEdgeColoring.RankThreeSharpChernoffScalar
import WeightedEdgeColoring.RankThreeSharpCollisionScalar
import WeightedEdgeColoring.RankThreeOriginalTypeNaturalIteration

/-!
# Concrete scalar data for the sharp round

This file fixes the proposal, gap, and error constants and makes natural
logarithmic choices for the row exponent and collision moment.  The checked
Chernoff and collision lemmas reduce construction of
`UniformSharpScalarData` to explicit ordinary inequalities in the current
parameters.
-/

namespace WeightedEdgeColoring

open SharpFixedSlackNumeric

/-- Four logarithms pay the cubic dependency budgets occurring in a sharp
round. -/
noncomputable def sharpConcreteZ (d : ℕ) : ℝ :=
  4 * Real.log ((d : ℝ) + 1)

/-- A logarithmic moment order for the quadratic collision statistic. -/
noncomputable def sharpConcreteMomentOrder (d : ℕ) : ℕ :=
  Nat.ceil (8 * Real.log ((d : ℝ) + 1))

noncomputable def sharpConcreteRho (d lambda : ℕ) : ℝ :=
  sharpScaledA lambda / (d : ℝ)

noncomputable def sharpConcreteSlotMean (d S lambda : ℕ) : ℝ :=
  sharpConcreteRho d lambda *
    (((S * (d + S - 3 * lambda) : ℕ) : ℝ) /
      ((3 * lambda : ℕ) : ℝ))

noncomputable def sharpConcreteSlotTarget (d lambda : ℕ) : ℝ :=
  (sharpScaledA lambda * (2 - sharpConcreteGamma) *
      (1 - sharpConcreteGamma) - sharpScaledEta lambda) * d /
    (3 * lambda : ℕ)

noncomputable def sharpConcreteSlotGap (d S lambda : ℕ) : ℝ :=
  sharpConcreteSlotMean d S lambda - sharpConcreteSlotTarget d lambda

noncomputable def sharpConcreteJobMean (d S lambda : ℕ) : ℝ :=
  sharpConcreteRho d lambda * ((d : ℝ) * (S : ℝ) / (lambda : ℝ))

noncomputable def sharpConcreteJobTarget (d lambda : ℕ) : ℝ :=
  (2 * sharpScaledA lambda * (1 - sharpConcreteGamma) +
    sharpScaledEta lambda) * d /
    (2 * lambda : ℕ)

noncomputable def sharpConcreteJobGap (d S lambda : ℕ) : ℝ :=
  sharpConcreteJobTarget d lambda - sharpConcreteJobMean d S lambda

noncomputable def sharpConcreteSlotTilt (d S lambda : ℕ) : ℝ :=
  sharpConcreteSlotGap d S lambda /
    (2 * sharpConcreteSlotMean d S lambda)

noncomputable def sharpConcreteJobTilt (d S lambda : ℕ) : ℝ :=
  sharpConcreteJobGap d S lambda /
    (2 * sharpConcreteJobMean d S lambda)

theorem sharpConcreteZ_pos (d : ℕ) (hd : 0 < d) :
    0 < sharpConcreteZ d := by
  have harg : (1 : ℝ) < (d : ℝ) + 1 := by
    exact_mod_cast (Nat.succ_lt_succ hd)
  exact mul_pos (by norm_num) (Real.log_pos harg)

/-- Padding to `floor (3d/4)` leaves a definite lower-tail gap once `d`
dominates the codegree.  The constant is intentionally generous. -/
theorem sharpConcrete_paddedSlotGap_lower
    (d lambda : ℕ) (hlambda : 0 < lambda)
    (hscale : 1000 * lambda ≤ d) :
    sharpScaledEta lambda * d / (6 * lambda : ℕ) ≤
      sharpConcreteSlotGap d
        (RankThreeOptionSystem.OriginalIterationState.fixedSlackPaddedSlotTarget
          sharpConcreteGamma d) lambda := by
  let S := RankThreeOptionSystem.OriginalIterationState.fixedSlackPaddedSlotTarget
    sharpConcreteGamma d
  change sharpScaledEta lambda * d / (6 * lambda : ℕ) ≤
    sharpConcreteSlotGap d S lambda
  have hd : 0 < d := lt_of_lt_of_le (by omega : 0 < 1000 * lambda) hscale
  have hSlo : (1 - sharpConcreteGamma) * (d : ℝ) - 1 < (S : ℝ) := by
    exact RankThreeOptionSystem.OriginalIterationState.fixedSlackPaddedSlotTarget_lower
      sharpConcreteGamma d
  have hsub : 3 * lambda ≤ d + S := by omega
  have hdR : (0 : ℝ) < d := by exact_mod_cast hd
  have hlR : (0 : ℝ) < lambda := by exact_mod_cast hlambda
  have hscaleR : (1000 : ℝ) * lambda ≤ d := by exact_mod_cast hscale
  have hlambda1R : (1 : ℝ) ≤ lambda := by exact_mod_cast hlambda
  have hSlo34 : (3 / 4 : ℝ) * d - 1 ≤ (S : ℝ) := by
    norm_num [sharpConcreteGamma] at hSlo
    exact hSlo.le
  have hleft0 : (0 : ℝ) ≤ (3 / 4 : ℝ) * d - 1 := by
    nlinarith
  have hright0 : (0 : ℝ) ≤
      (d : ℝ) + ((3 / 4 : ℝ) * d - 1) - 3 * lambda := by
    nlinarith
  have hright_le :
      (d : ℝ) + ((3 / 4 : ℝ) * d - 1) - 3 * lambda ≤
        (d : ℝ) + S - 3 * lambda := by
    linarith
  have hprodLower :
      ((3 / 4 : ℝ) * d - 1) *
          ((d : ℝ) + ((3 / 4 : ℝ) * d - 1) - 3 * lambda) ≤
        (S : ℝ) * ((d : ℝ) + S - 3 * lambda) := by
    exact mul_le_mul hSlo34 hright_le hright0 (Nat.cast_nonneg S)
  have hscaleDiv : (lambda : ℝ) ≤ (d : ℝ) / 1000 := by
    linarith
  have hdlambda : (d : ℝ) * lambda ≤ (d : ℝ) ^ 2 / 1000 := by
    have := mul_le_mul_of_nonneg_left hscaleDiv hdR.le
    nlinarith
  have hcast : ((S * (d + S - 3 * lambda) : ℕ) : ℝ) =
      (S : ℝ) * ((d : ℝ) + (S : ℝ) - 3 * (lambda : ℝ)) := by
    rw [Nat.cast_mul, Nat.cast_sub hsub]
    push_cast
    ring
  dsimp [sharpConcreteSlotGap, sharpConcreteSlotMean,
    sharpConcreteSlotTarget, sharpConcreteRho]
  rw [hcast]
  push_cast
  norm_num [sharpScaledA, sharpScaledAlpha, sharpScaledEta,
    sharpConcreteGamma] at hSlo ⊢
  field_simp
  nlinarith [hprodLower, hdlambda]

theorem sharpConcrete_paddedSlotChernoffData
    (d lambda : ℕ) (hlambda : 0 < lambda)
    (hscale : 1000 * lambda ≤ d) :
    let S := RankThreeOptionSystem.OriginalIterationState.fixedSlackPaddedSlotTarget
      sharpConcreteGamma d
    0 < sharpConcreteSlotMean d S lambda ∧
      0 ≤ sharpConcreteSlotGap d S lambda ∧
      sharpConcreteSlotGap d S lambda ≤
        2 * sharpConcreteSlotMean d S lambda := by
  let S := RankThreeOptionSystem.OriginalIterationState.fixedSlackPaddedSlotTarget
    sharpConcreteGamma d
  change 0 < sharpConcreteSlotMean d S lambda ∧
    0 ≤ sharpConcreteSlotGap d S lambda ∧
    sharpConcreteSlotGap d S lambda ≤ 2 * sharpConcreteSlotMean d S lambda
  have hd : 0 < d := lt_of_lt_of_le (by omega : 0 < 1000 * lambda) hscale
  have hgap := sharpConcrete_paddedSlotGap_lower d lambda hlambda hscale
  have hpiecePos : 0 < sharpScaledEta lambda * d / (6 * lambda : ℕ) := by
    have heta := (sharpScaled_constants lambda hlambda).2.1
    positivity
  have htarget0 : 0 ≤ sharpConcreteSlotTarget d lambda := by
    unfold sharpConcreteSlotTarget
    have hcoef : 0 < sharpScaledA lambda * (2 - sharpConcreteGamma) *
        (1 - sharpConcreteGamma) - sharpScaledEta lambda := by
      have ha := (sharpScaled_constants lambda hlambda).1
      norm_num [sharpScaledEta, sharpConcreteGamma]
      nlinarith
    positivity
  have hgapPos : 0 < sharpConcreteSlotGap d S lambda :=
    hpiecePos.trans_le hgap
  have hmeanPos : 0 < sharpConcreteSlotMean d S lambda := by
    dsimp [sharpConcreteSlotGap] at hgapPos
    linarith
  refine ⟨hmeanPos, hgapPos.le, ?_⟩
  dsimp [sharpConcreteSlotGap]
  linarith

theorem sharpConcrete_paddedJobChernoffData
    (d lambda : ℕ) (hlambda : 0 < lambda)
    (hscale : 1000 * lambda ≤ d) :
    let S := RankThreeOptionSystem.OriginalIterationState.fixedSlackPaddedSlotTarget
      sharpConcreteGamma d
    0 < sharpConcreteJobMean d S lambda ∧
      0 ≤ sharpConcreteJobGap d S lambda ∧
      sharpConcreteJobGap d S lambda ≤
        2 * sharpConcreteJobMean d S lambda := by
  let S := RankThreeOptionSystem.OriginalIterationState.fixedSlackPaddedSlotTarget
    sharpConcreteGamma d
  change 0 < sharpConcreteJobMean d S lambda ∧
    0 ≤ sharpConcreteJobGap d S lambda ∧
    sharpConcreteJobGap d S lambda ≤ 2 * sharpConcreteJobMean d S lambda
  have hd : 0 < d := lt_of_lt_of_le (by omega : 0 < 1000 * lambda) hscale
  have hSlo : (1 - sharpConcreteGamma) * (d : ℝ) - 1 < (S : ℝ) := by
    exact RankThreeOptionSystem.OriginalIterationState.fixedSlackPaddedSlotTarget_lower
      sharpConcreteGamma d
  have hShi : (S : ℝ) ≤ (1 - sharpConcreteGamma) * d := by
    exact Nat.floor_le (by
      have : (0 : ℝ) ≤ 1 - sharpConcreteGamma := by
        norm_num [sharpConcreteGamma]
      positivity)
  have hdR : (0 : ℝ) < d := by exact_mod_cast hd
  have hlR : (0 : ℝ) < lambda := by exact_mod_cast hlambda
  have hscaleR : (1000 : ℝ) * lambda ≤ d := by exact_mod_cast hscale
  have hlambda1R : (1 : ℝ) ≤ lambda := by exact_mod_cast hlambda
  have hmeanPos : 0 < sharpConcreteJobMean d S lambda := by
    unfold sharpConcreteJobMean sharpConcreteRho
    have ha := (sharpScaled_constants lambda hlambda).1
    have hSpos : (0 : ℝ) < S := by
      norm_num [sharpConcreteGamma] at hSlo
      nlinarith
    positivity
  have hgap0 : 0 ≤ sharpConcreteJobGap d S lambda := by
    dsimp [sharpConcreteJobGap, sharpConcreteJobTarget,
      sharpConcreteJobMean, sharpConcreteRho]
    norm_num [sharpScaledA, sharpScaledAlpha, sharpScaledEta,
      sharpConcreteGamma] at hShi ⊢
    field_simp
    nlinarith
  refine ⟨hmeanPos, hgap0, ?_⟩
  dsimp [sharpConcreteJobGap, sharpConcreteJobTarget,
    sharpConcreteJobMean, sharpConcreteRho]
  norm_num [sharpScaledA, sharpScaledAlpha, sharpScaledEta,
    sharpConcreteGamma] at hSlo ⊢
  field_simp
  nlinarith

end WeightedEdgeColoring

namespace WeightedEdgeColoring.RankThreeOptionSystem

open scoped BigOperators
open WeightedEdgeColoring.SharpFixedSlackNumeric

universe u v w x

variable {Job : Type u} {Slot : Type v} {Option : Type w}
  [Fintype Job] [Fintype Slot] [Fintype Option]
  [DecidableEq Job] [DecidableEq Slot] [DecidableEq Option]
  {Group : Type x} [Fintype Group] [DecidableEq Group]

namespace OriginalIterationState.UniformSharpScalarData

/-- Concrete fixed-constant construction.  Every remaining premise is an
explicit inequality between the displayed current parameters.  In
particular, the graph-dependent Chernoff means and the collision moment no
longer occur among the hypotheses. -/
noncomputable def ofSharpConcreteRegular
    (H : RankThreeOptionSystem Job Slot Option)
    (members : Group → Finset Job)
    (lambda d S R K m : ℕ)
    (hd : 0 < d) (hlambda : 0 < lambda)
    (htwo : ∀ o, (H.slots o).card = 2)
    (hjob : ∀ j, (H.fiber j).card = d)
    (hslot : ∀ s, H.slotDegree s = S)
    (hjobSlot : ∀ j s, H.jobSlotCodegree j s ≤ lambda)
    (hslotPair : ∀ s t, s ≠ t → H.slotPairCodegree s t ≤ lambda)
    (hslotMean : 0 < sharpConcreteSlotMean d S lambda)
    (hslotGap0 : 0 ≤ sharpConcreteSlotGap d S lambda)
    (hslotGap : sharpConcreteSlotGap d S lambda ≤
      2 * sharpConcreteSlotMean d S lambda)
    (hjobMean : 0 < sharpConcreteJobMean d S lambda)
    (hjobGap0 : 0 ≤ sharpConcreteJobGap d S lambda)
    (hjobGap : sharpConcreteJobGap d S lambda ≤
      2 * sharpConcreteJobMean d S lambda)
    (hrowCap : exponentialRowWeight (sharpConcreteZ d) ≤
      increasingCap (sharpConcreteRho d lambda))
    (hcollisionCap : collisionWeight (sharpConcreteMomentOrder d) ≤
      increasingCap (sharpConcreteRho d lambda))
    (hpairProduct : exponentialRowWeight (sharpConcreteZ d) *
      (pairNeighborBudget R d : ℝ) ≤ 1 / 2)
    (hgroupRate : sharpConcreteZ d +
        2 * increasingCap (sharpConcreteRho d lambda) *
          (lowerNeighborBudget (groupSupportBudget K d) d : ℝ) ≤
      -(sharpConcreteDelta * (1 - sharpConcreteDelta) +
          (Real.exp (-sharpConcreteDelta) - 1)) *
        (sharpConcreteRho d lambda * (m : ℝ)))
    (hslotRate : sharpConcreteZ d +
        2 * increasingCap (sharpConcreteRho d lambda) *
          (lowerNeighborBudget (slotSupportBudget d) d : ℝ) ≤
      sharpConcreteSlotGap d S lambda ^ 2 /
        (4 * sharpConcreteSlotMean d S lambda))
    (hupperRate : sharpConcreteZ d + Real.log 2 ≤
      sharpConcreteJobGap d S lambda ^ 2 /
        (4 * sharpConcreteJobMean d S lambda))
    (hupperProduct : exponentialRowWeight (sharpConcreteZ d) *
      (increasingNeighborBudget (upperSupportBudget d) R d : ℝ) ≤ 1 / 2)
    (hcollisionCorrection :
      36 * sharpScaledA lambda * sharpConcreteMomentOrder d * lambda +
          12 * sharpConcreteMomentOrder d ^ 2 * lambda ≤
        sharpScaledEta lambda * d / 2)
    (hcollisionProduct : exponentialRowWeight (sharpConcreteZ d) *
      (increasingNeighborBudget (slotSupportBudget d) R d : ℝ) ≤ 1 / 2) :
    OriginalIterationState.UniformSharpScalarData
      H members lambda d d R K m (sharpConcreteMomentOrder d)
      (sharpConcreteRho d lambda) (sharpScaledA lambda) sharpConcreteGamma
      (sharpScaledEta lambda) (sharpScaledEta lambda) (sharpScaledEta lambda)
      (sharpConcreteZ d) sharpConcreteDelta := by
  let rho := sharpConcreteRho d lambda
  let z := sharpConcreteZ d
  let k := sharpConcreteMomentOrder d
  let Ms := sharpConcreteSlotMean d S lambda
  let ts := sharpConcreteSlotGap d S lambda
  let Mj := sharpConcreteJobMean d S lambda
  let tj := sharpConcreteJobGap d S lambda
  let slotTilt := sharpConcreteSlotTilt d S lambda
  let jobTilt := sharpConcreteJobTilt d S lambda
  have hrho := sharpScaled_rho_bounds lambda d hlambda hd
  have hslotTilt0 : 0 ≤ slotTilt := by
    dsimp [slotTilt, sharpConcreteSlotTilt]
    positivity
  have hjobTilt0 : 0 ≤ jobTilt := by
    dsimp [jobTilt, sharpConcreteJobTilt]
    positivity
  have hgroupExponent :
      Real.exp
          ((sharpConcreteDelta * (1 - sharpConcreteDelta) +
              (Real.exp (-sharpConcreteDelta) - 1)) *
            (rho * (m : ℝ))) ≤
        Real.exp (-(z + 2 * increasingCap rho *
          (lowerNeighborBudget (groupSupportBudget K d) d : ℝ))) := by
    apply Real.exp_le_exp.mpr
    dsimp [rho, z]
    linarith
  have hslotExponent :
      Real.exp (slotTilt * sharpConcreteSlotTarget d lambda +
          (Real.exp (-slotTilt) - 1) * Ms) ≤
        Real.exp (-(z + 2 * increasingCap rho *
          (lowerNeighborBudget (slotSupportBudget d) d : ℝ))) := by
    have hchernoff := lower_chernoff_scalar_le Ms ts hslotMean hslotGap0 hslotGap
    have htarget : sharpConcreteSlotTarget d lambda = Ms - ts := by
      simp [Ms, ts, sharpConcreteSlotGap]
    have htilt : slotTilt = ts / (2 * Ms) := by
      rfl
    rw [htarget, htilt]
    exact hchernoff.trans (by
      simpa [neg_div] using (exp_neg_quadratic_pays
        (ts ^ 2 / (4 * Ms)) z
        (2 * increasingCap rho *
          (lowerNeighborBudget (slotSupportBudget d) d : ℝ)) hslotRate))
  have hupperExponent :
      Real.exp (-jobTilt * sharpConcreteJobTarget d lambda +
          (Real.exp jobTilt - 1) * Mj) ≤
        exponentialRowWeight z / 2 := by
    have hchernoff := upper_chernoff_scalar_le Mj tj hjobMean hjobGap0 hjobGap
    have htarget : sharpConcreteJobTarget d lambda = Mj + tj := by
      simp [Mj, tj, sharpConcreteJobGap]
    have htilt : jobTilt = tj / (2 * Mj) := by
      rfl
    rw [htarget, htilt]
    calc
      Real.exp
          (-(tj / (2 * Mj)) * (Mj + tj) +
            (Real.exp (tj / (2 * Mj)) - 1) * Mj) ≤
          Real.exp (-(tj ^ 2) / (4 * Mj)) := hchernoff
      _ ≤ Real.exp (-(z + Real.log 2)) :=
        by simpa [neg_div] using
          (exp_neg_quadratic_pays (tj ^ 2 / (4 * Mj)) z (Real.log 2)
            hupperRate)
      _ = exponentialRowWeight z / 2 := by
        rw [show -(z + Real.log 2) = -z - Real.log 2 by ring,
          Real.exp_sub, Real.exp_log (by norm_num : (0 : ℝ) < 2)]
        rfl
  have hcollisionEnvelope :
      slotCollisionMomentEnvelope rho d d lambda k ≤
        sharpScaledEta lambda * d := by
    exact slotCollisionMomentEnvelope_uniform_le_of_split
      (sharpScaledA lambda) (sharpScaledEta lambda) d lambda k hd
      (sharpScaled_constants lambda hlambda).2.2.2.2.2
      hcollisionCorrection
  apply ofRegularBounds H members lambda d S R K m k
    rho (sharpScaledA lambda) sharpConcreteGamma (sharpScaledEta lambda)
    (sharpScaledEta lambda) (sharpScaledEta lambda) z sharpConcreteDelta
    slotTilt jobTilt hlambda
  · simpa [rho, sharpConcreteRho] using hrho.1
  · simpa [rho, sharpConcreteRho] using hrho.2.1
  · rfl
  · exact htwo
  · exact hjob
  · exact hslot
  · exact hjobSlot
  · exact hslotPair
  · exact sharpConcrete_constants.2.2.2.2.1
  · exact hslotTilt0
  · exact hjobTilt0
  · exact sharpConcreteZ_pos d hd
  · simpa [rho, sharpConcreteRho] using hrho.2.2
  · exact hrowCap
  · exact hcollisionCap
  · exact hpairProduct
  · exact hgroupExponent
  · simpa [slotTilt, Ms, rho, sharpConcreteSlotMean,
      sharpConcreteSlotTarget] using hslotExponent
  · simpa [jobTilt, Mj, rho, sharpConcreteJobMean,
      sharpConcreteJobTarget] using hupperExponent
  · exact hupperProduct
  · exact sharpScaled_collisionThreshold_pos lambda d hlambda hd
  · exact hcollisionEnvelope
  · exact hcollisionProduct

/-- Specialization used by the iteration: cyclic padding makes every slot
have degree `floor ((1-gamma)d)`.  The simple scale assumption
`1000*lambda ≤ d` now supplies both Chernoff mean-gap packages. -/
noncomputable def ofSharpConcretePadded
    (H : RankThreeOptionSystem Job Slot Option)
    (members : Group → Finset Job)
    (lambda d R K m : ℕ)
    (hd : 0 < d) (hlambda : 0 < lambda)
    (hscale : 1000 * lambda ≤ d)
    (htwo : ∀ o, (H.slots o).card = 2)
    (hjob : ∀ j, (H.fiber j).card = d)
    (hslot : ∀ s, H.slotDegree s =
      fixedSlackPaddedSlotTarget sharpConcreteGamma d)
    (hjobSlot : ∀ j s, H.jobSlotCodegree j s ≤ lambda)
    (hslotPair : ∀ s t, s ≠ t → H.slotPairCodegree s t ≤ lambda)
    (hrowCap : exponentialRowWeight (sharpConcreteZ d) ≤
      increasingCap (sharpConcreteRho d lambda))
    (hcollisionCap : collisionWeight (sharpConcreteMomentOrder d) ≤
      increasingCap (sharpConcreteRho d lambda))
    (hpairProduct : exponentialRowWeight (sharpConcreteZ d) *
      (pairNeighborBudget R d : ℝ) ≤ 1 / 2)
    (hgroupRate : sharpConcreteZ d +
        2 * increasingCap (sharpConcreteRho d lambda) *
          (lowerNeighborBudget (groupSupportBudget K d) d : ℝ) ≤
      -(sharpConcreteDelta * (1 - sharpConcreteDelta) +
          (Real.exp (-sharpConcreteDelta) - 1)) *
        (sharpConcreteRho d lambda * (m : ℝ)))
    (hslotRate : sharpConcreteZ d +
        2 * increasingCap (sharpConcreteRho d lambda) *
          (lowerNeighborBudget (slotSupportBudget d) d : ℝ) ≤
      sharpConcreteSlotGap d
          (fixedSlackPaddedSlotTarget sharpConcreteGamma d) lambda ^ 2 /
        (4 * sharpConcreteSlotMean d
          (fixedSlackPaddedSlotTarget sharpConcreteGamma d) lambda))
    (hupperRate : sharpConcreteZ d + Real.log 2 ≤
      sharpConcreteJobGap d
          (fixedSlackPaddedSlotTarget sharpConcreteGamma d) lambda ^ 2 /
        (4 * sharpConcreteJobMean d
          (fixedSlackPaddedSlotTarget sharpConcreteGamma d) lambda))
    (hupperProduct : exponentialRowWeight (sharpConcreteZ d) *
      (increasingNeighborBudget (upperSupportBudget d) R d : ℝ) ≤ 1 / 2)
    (hcollisionCorrection :
      36 * sharpScaledA lambda * sharpConcreteMomentOrder d * lambda +
          12 * sharpConcreteMomentOrder d ^ 2 * lambda ≤
        sharpScaledEta lambda * d / 2)
    (hcollisionProduct : exponentialRowWeight (sharpConcreteZ d) *
      (increasingNeighborBudget (slotSupportBudget d) R d : ℝ) ≤ 1 / 2) :
    OriginalIterationState.UniformSharpScalarData
      H members lambda d d R K m (sharpConcreteMomentOrder d)
      (sharpConcreteRho d lambda) (sharpScaledA lambda) sharpConcreteGamma
      (sharpScaledEta lambda) (sharpScaledEta lambda) (sharpScaledEta lambda)
      (sharpConcreteZ d) sharpConcreteDelta := by
  let S := fixedSlackPaddedSlotTarget sharpConcreteGamma d
  have hs := sharpConcrete_paddedSlotChernoffData d lambda hlambda hscale
  have hj := sharpConcrete_paddedJobChernoffData d lambda hlambda hscale
  exact ofSharpConcreteRegular H members lambda d S R K m hd hlambda
    htwo hjob hslot hjobSlot hslotPair hs.1 hs.2.1 hs.2.2
    hj.1 hj.2.1 hj.2.2 hrowCap hcollisionCap hpairProduct hgroupRate
    hslotRate hupperRate hupperProduct hcollisionCorrection hcollisionProduct

end OriginalIterationState.UniformSharpScalarData
end WeightedEdgeColoring.RankThreeOptionSystem
