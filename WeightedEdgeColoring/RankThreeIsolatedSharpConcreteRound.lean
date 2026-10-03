import WeightedEdgeColoring.RankThreeIsolatedSharpUniform
import WeightedEdgeColoring.RankThreeIsolatedSharpScalar

/-!
# Concrete padded isolated round

This file substitutes the fixed scaled constants, the padded slot degree,
and the logarithmic moment choices into the uniform isolated theorem.  Its
hypotheses are now only explicit scalar inequalities in `d`, `lambda`, the
endpoint-block parameters, and the chosen logarithmic order.
-/

namespace WeightedEdgeColoring.RankThreeOptionSystem

open scoped BigOperators
open WeightedEdgeColoring.SharpFixedSlackNumeric

universe u v w x

variable {Job : Type u} {Slot : Type v} {Option : Type w} {Group : Type x}
  [Fintype Job] [Fintype Slot] [Fintype Option] [Fintype Group]
  [DecidableEq Job] [DecidableEq Slot] [DecidableEq Option] [DecidableEq Group]
  (H : RankThreeOptionSystem Job Slot Option)

/-- The extra slot-row isolation allowance still fits the fixed-slack
budget. -/
theorem sharpScaled_isolated_error_fits (lambda : ℕ) (hlambda : 0 < lambda) :
    (1 - sharpConcreteGamma) * sharpScaledEta lambda +
        2 * sharpScaledEta lambda + sharpScaledEta lambda ≤
      sharpScaledA lambda * sharpConcreteGamma *
        (1 - sharpConcreteGamma) := by
  have ha := (sharpScaled_constants lambda hlambda).1
  have ha1 : sharpScaledA lambda ≤ 1 := by
    simpa using (sharpScaled_rho_bounds lambda 1 hlambda (by omega)).2.1
  have hlR : (1 : ℝ) ≤ lambda := by exact_mod_cast hlambda
  have haSmall : sharpScaledA lambda ≤ sharpScaledAlpha := by
    unfold sharpScaledA
    have halpha0 : 0 ≤ sharpScaledAlpha := by norm_num [sharpScaledAlpha]
    apply (div_le_iff₀ (by positivity : (0 : ℝ) < lambda)).2
    have := mul_le_mul_of_nonneg_left hlR halpha0
    simpa using this
  norm_num [sharpScaledEta, sharpConcreteGamma] at ⊢
  nlinarith

theorem sharpScaled_isolated_slotRate_pos (lambda : ℕ) (hlambda : 0 < lambda) :
    0 < WeightedEdgeColoring.fixedSlackSlotRetention (sharpScaledA lambda)
          sharpConcreteGamma * (1 - sharpConcreteGamma) +
        2 * sharpScaledEta lambda + sharpScaledEta lambda := by
  have ha := (sharpScaled_constants lambda hlambda).1
  have ha1 : sharpScaledA lambda ≤ 1 := by
    simpa using (sharpScaled_rho_bounds lambda 1 hlambda (by omega)).2.1
  have hlR : (1 : ℝ) ≤ lambda := by exact_mod_cast hlambda
  have haSmall : sharpScaledA lambda ≤ sharpScaledAlpha := by
    unfold sharpScaledA
    have halpha0 : 0 ≤ sharpScaledAlpha := by norm_num [sharpScaledAlpha]
    apply (div_le_iff₀ (by positivity : (0 : ℝ) < lambda)).2
    have := mul_le_mul_of_nonneg_left hlR halpha0
    simpa using this
  unfold WeightedEdgeColoring.fixedSlackSlotRetention
  norm_num [sharpScaledEta, sharpConcreteGamma, sharpScaledAlpha] at haSmall ⊢
  nlinarith

/-- Fixed room reserved for the squared-codegree logarithmic correction. -/
noncomputable def sharpIsolationBeta0 : ℝ := 1 / 1000000000000000

/-- A simple integral block-size multiplier which absorbs the additive
`4*k^2` isolation moment. -/
def sharpEndpointBlockFactor : ℕ := 3000000000000

theorem sharpIsolation_fixed_budget :
    18 * sharpScaledAlpha ^ 2 +
        (72 * sharpScaledAlpha + 24) * sharpIsolationBeta0 ≤
      sharpScaledAlpha / 64 := by
  norm_num [sharpScaledAlpha, sharpIsolationBeta0]

theorem sharpScaled_isolationBudget_of_square_ratio
    (d lambda : ℕ) (hd : 0 < d) (hlambda : 0 < lambda)
    (hratio : (lambda : ℝ) ^ 2 * sharpConcreteMomentUpper d ^ 2 ≤
      sharpIsolationBeta0 * d) :
    18 * sharpScaledA lambda ^ 2 * d +
        72 * sharpScaledA lambda * sharpConcreteMomentOrder d * lambda +
        24 * sharpConcreteMomentOrder d ^ 2 * lambda ≤
      sharpScaledEta lambda * d := by
  simpa [sharpScaledA, sharpScaledEta] using
    isolatedLoss_scaled_of_squared_codegree_ratio
      sharpScaledAlpha sharpIsolationBeta0 d lambda hd hlambda
      (by norm_num [sharpScaledAlpha])
      (by norm_num [sharpIsolationBeta0]) hratio sharpIsolation_fixed_budget

/-- The natural endpoint choice `K = Theta(lambda*k^2)` pays the group
isolation loss.  Endpoint groups have at most `2K` jobs and at least `K*d`
options, which explains the two occurrences of `K` below. -/
theorem sharpScaled_groupLossEnvelope_of_blockScale
    (d lambda K k : ℕ) (hd : 0 < d) (hlambda : 0 < lambda)
    (hk : 0 < k)
    (hK : sharpEndpointBlockFactor * lambda * k ^ 2 ≤ K) :
    isolatedRowConflictWeightedMomentEnvelope
        (sharpScaledA lambda / (d : ℝ)) ((2 * K : ℕ) * d)
          (3 * d) k ≤
      ((sharpConcreteDelta / 2) *
        (sharpScaledA lambda / (d : ℝ)) * (K * d : ℕ)) / 2 := by
  have hdR : (0 : ℝ) < d := by exact_mod_cast hd
  have hlR : (1 : ℝ) ≤ lambda := by exact_mod_cast hlambda
  have hkR : (1 : ℝ) ≤ k := by exact_mod_cast hk
  have hKR : (sharpEndpointBlockFactor : ℝ) * lambda * (k : ℝ) ^ 2 ≤ K := by
    exact_mod_cast hK
  have haPos : 0 < sharpScaledA lambda :=
    (sharpScaled_constants lambda hlambda).1
  have haSmall : sharpScaledA lambda ≤ sharpScaledAlpha := by
    unfold sharpScaledA
    have halpha0 : 0 ≤ sharpScaledAlpha := by
      norm_num [sharpScaledAlpha]
    have hmul := mul_le_mul_of_nonneg_left hlR halpha0
    exact (div_le_iff₀ (by positivity : (0 : ℝ) < lambda)).2 (by
      simpa using hmul)
  have hidentity :
      isolatedRowConflictWeightedMomentEnvelope
          (sharpScaledA lambda / (d : ℝ)) ((2 * K : ℕ) * d)
            (3 * d) k =
        6 * sharpScaledA lambda ^ 2 * K +
          12 * sharpScaledA lambda * k + 4 * k ^ 2 := by
    unfold isolatedRowConflictWeightedMomentEnvelope
    push_cast
    field_simp
    ring
  rw [hidentity]
  norm_num [sharpConcreteDelta]
  have hlarge : 300 * (k : ℝ) ^ 2 ≤
      sharpScaledA lambda * K := by
    unfold sharpScaledA sharpScaledAlpha sharpEndpointBlockFactor at *
    have hlpos : (0 : ℝ) < lambda := by positivity
    calc
      300 * (k : ℝ) ^ 2 =
          (1 / 10000000000 : ℝ) *
            (3000000000000 * lambda * (k : ℝ) ^ 2) / lambda := by
              field_simp
              ring
      _ ≤ (1 / 10000000000 : ℝ) * K / lambda := by
        have hKR' : (3000000000000 : ℝ) * lambda * (k : ℝ) ^ 2 ≤ K := by
          simpa [sharpEndpointBlockFactor] using hKR
        gcongr
      _ = (1 / 10000000000 / lambda) * K := by ring
  have hkSq : (k : ℝ) ≤ k ^ 2 := by nlinarith
  have hmean : 6 * sharpScaledA lambda ^ 2 * K ≤
      (1 / 1000000000 : ℝ) * (sharpScaledA lambda * K) := by
    have hfac : 0 ≤ sharpScaledA lambda * (K : ℝ) := by positivity
    have := mul_le_mul_of_nonneg_right haSmall hfac
    norm_num [sharpScaledAlpha] at this ⊢
    nlinarith
  have hlinear : 12 * sharpScaledA lambda * k ≤ 12 * k ^ 2 := by
    have ha1 : sharpScaledA lambda ≤ 1 := haSmall.trans (by
      norm_num [sharpScaledAlpha])
    nlinarith [mul_le_mul_of_nonneg_right ha1 (show (0 : ℝ) ≤ k by positivity)]
  have hrhs :
      (1 / 4 : ℝ) * (sharpScaledA lambda / (d : ℝ)) *
          ((K : ℝ) * (d : ℝ)) / 2 = sharpScaledA lambda * K / 8 := by
    field_simp
    ring
  rw [hrhs]
  nlinarith

/-- The chosen endpoint block is sublinear on the square-root palette
scale.  Here `r` bounds the codegree, `r^2` is below the palette size, and
the current quantized degree grows polynomially in `r`. -/
theorem eventually_sharpEndpointBlockSize_sublinear
    (C : ℕ) (epsilon : ℝ) (hepsilon : 0 < epsilon) :
    ∀ᶠ r : ℕ in Filter.atTop, ∀ n d lambda : ℕ,
      0 < d → 0 < r → lambda ≤ r → r ^ 2 ≤ n →
      d ≤ (r + 1) ^ C →
      (sharpEndpointBlockFactor * lambda *
          sharpConcreteMomentOrder d ^ 2 : ℕ) ≤ epsilon * n := by
  have hfactorPos : (0 : ℝ) < sharpEndpointBlockFactor := by
    norm_num [sharpEndpointBlockFactor]
  have hepsFactor : 0 < epsilon / sharpEndpointBlockFactor :=
    div_pos hepsilon hfactorPos
  have hB0 : (0 : ℝ) ≤ 8 * (C : ℝ) + 10 := by positivity
  filter_upwards [eventually_mul_log_sq_le_linear
      (8 * (C : ℝ) + 10) (epsilon / sharpEndpointBlockFactor)
        hB0 hepsFactor,
      Filter.eventually_ge_atTop (1 : ℕ)] with r hsquare hr
  intro n d lambda hd _hr hlambda hn hpoly
  have hk := sharpConcreteMomentOrder_cast_le d hd
  have hU := sharpConcreteMomentUpper_le_of_polynomial_growth d r C hr hpoly
  have hklog : (sharpConcreteMomentOrder d : ℝ) ≤
      (8 * (C : ℝ) + 10) * Real.log ((r : ℝ) + 1) := hk.trans hU
  have hk0 : (0 : ℝ) ≤ sharpConcreteMomentOrder d := by positivity
  have hksq := pow_le_pow_left₀ hk0 hklog 2
  have hscaled : (sharpEndpointBlockFactor : ℝ) *
      sharpConcreteMomentOrder d ^ 2 ≤ epsilon * r := by
    have := mul_le_mul_of_nonneg_left hksq
      (show (0 : ℝ) ≤ sharpEndpointBlockFactor by positivity)
    have hsquare' := mul_le_mul_of_nonneg_left hsquare
      (show (0 : ℝ) ≤ sharpEndpointBlockFactor by positivity)
    dsimp [sharpEndpointBlockFactor] at hsquare' ⊢
    nlinarith
  have hlambdaR : (lambda : ℝ) ≤ r := by exact_mod_cast hlambda
  have hnR : (r : ℝ) ^ 2 ≤ n := by exact_mod_cast hn
  have hr0 : (0 : ℝ) ≤ r := by positivity
  have htotal : (sharpEndpointBlockFactor : ℝ) * lambda *
      sharpConcreteMomentOrder d ^ 2 ≤ epsilon * n := by
    calc
      (sharpEndpointBlockFactor : ℝ) * lambda *
          sharpConcreteMomentOrder d ^ 2 ≤
        ((sharpEndpointBlockFactor : ℝ) *
          sharpConcreteMomentOrder d ^ 2) * r := by
            nlinarith [mul_le_mul_of_nonneg_left hlambdaR
              (show (0 : ℝ) ≤
                sharpEndpointBlockFactor * sharpConcreteMomentOrder d ^ 2 by
                  positivity)]
      _ ≤ (epsilon * r) * r := by
        exact mul_le_mul_of_nonneg_right hscaled hr0
      _ ≤ epsilon * n := by
        nlinarith
  exact_mod_cast htotal

/-- The same cube-root scale satisfies the squared-codegree isolation
condition: `lambda ≤ r`, `r^3 ≤ d`, and polynomial growth of `d` are
enough eventually. -/
theorem eventually_sharpIsolation_square_ratio_cube_scale (C : ℕ) :
    ∀ᶠ r : ℕ in Filter.atTop, ∀ d lambda : ℕ,
      0 < d → 0 < r → lambda ≤ r → r ^ 3 ≤ d →
      d ≤ (r + 1) ^ C →
      (lambda : ℝ) ^ 2 * sharpConcreteMomentUpper d ^ 2 ≤
        sharpIsolationBeta0 * d := by
  have hB0 : (0 : ℝ) ≤ 8 * (C : ℝ) + 10 := by positivity
  have hbeta : 0 < sharpIsolationBeta0 := by
    norm_num [sharpIsolationBeta0]
  filter_upwards [eventually_mul_log_sq_le_linear
      (8 * (C : ℝ) + 10) sharpIsolationBeta0 hB0 hbeta,
      Filter.eventually_ge_atTop (1 : ℕ)] with r hsquare hr
  intro d lambda hd _hr hlambda hdlower hdupper
  have hU := sharpConcreteMomentUpper_le_of_polynomial_growth d r C hr hdupper
  have hU0 : 0 ≤ sharpConcreteMomentUpper d :=
    le_trans (by norm_num) (sharpConcreteMomentUpper_one_le d hd)
  have hUsq : sharpConcreteMomentUpper d ^ 2 ≤
      ((8 * (C : ℝ) + 10) * Real.log ((r : ℝ) + 1)) ^ 2 :=
    pow_le_pow_left₀ hU0 hU 2
  have hlambdaR : (lambda : ℝ) ≤ r := by exact_mod_cast hlambda
  have hr0 : (0 : ℝ) ≤ r := by positivity
  have hlambdaSq : (lambda : ℝ) ^ 2 ≤ r ^ 2 :=
    pow_le_pow_left₀ (by positivity) hlambdaR 2
  have hdlowerR : (r : ℝ) ^ 3 ≤ d := by exact_mod_cast hdlower
  calc
    (lambda : ℝ) ^ 2 * sharpConcreteMomentUpper d ^ 2 ≤
        r ^ 2 *
          ((8 * (C : ℝ) + 10) * Real.log ((r : ℝ) + 1)) ^ 2 := by
      gcongr
    _ ≤ r ^ 2 * (sharpIsolationBeta0 * r) := by gcongr
    _ = sharpIsolationBeta0 * r ^ 3 := by ring
    _ ≤ sharpIsolationBeta0 * d :=
      mul_le_mul_of_nonneg_left hdlowerR hbeta.le

/-- Every collision correction required by the old slot statistic is
already contained in the stronger isolation-loss budget. -/
theorem collisionCorrection_of_isolationBudget
    (a eta : ℝ) (d lambda k : ℕ) (ha0 : 0 ≤ a)
    (h : 18 * a ^ 2 * d + 72 * a * k * lambda +
        24 * k ^ 2 * lambda ≤ eta * d) :
    36 * a * k * lambda + 12 * k ^ 2 * lambda ≤ eta * d / 2 := by
  have hmean : 0 ≤ 18 * a ^ 2 * (d : ℝ) := by positivity
  push_cast at h ⊢
  nlinarith

/-- One concrete retained round on an exactly regular padded system.

The common isolation budget is the single quadratic inequality
`hIsolationBudget`.  The six other displayed assumptions bound the
Chernoff or Harris costs which depend on the current endpoint block size
and degree. -/
theorem exists_isolatedSharpFixedSlackRound_sharpConcretePadded
    (members : Group → Finset Job)
    (lambda d R K m : ℕ)
    (hd : 0 < d) (hlambda : 0 < lambda) (hm : 0 < m)
    (hscale : 1000 * lambda ≤ d)
    (htwo : ∀ o, (H.slots o).card = 2)
    (hjob : ∀ j, (H.fiber j).card = d)
    (hslot : ∀ s, H.slotDegree s =
      OriginalIterationState.fixedSlackPaddedSlotTarget
        sharpConcreteGamma d)
    (hjobSlot : ∀ j s, H.jobSlotCodegree j s ≤ lambda)
    (hslotPair : ∀ s t, s ≠ t → H.slotPairCodegree s t ≤ lambda)
    (hmembers : ∀ g, (members g).card ≤ K)
    (hgroupSupportLower : ∀ g,
      m ≤ (linearRowSupport
        (H.jobGroupCoverageWeight members) g).card)
    (hgroupIncidence : ∀ j,
      ((Finset.univ : Finset Group).filter
        (fun g ↦ j ∈ members g)).card ≤ R)
    (hrowHalf : exponentialRowWeight (sharpConcreteZ d) ≤ 1 / 2)
    (hcollisionRow : collisionWeight (sharpConcreteMomentOrder d) ≤
      exponentialRowWeight (sharpConcreteZ d))
    (hgroupRate : sharpConcreteZ d +
        2 * exponentialRowWeight (sharpConcreteZ d) *
          (isolatedLowerNeighborBudget (groupSupportBudget K d) R d : ℝ) ≤
      -(((sharpConcreteDelta / 2) * (1 - sharpConcreteDelta / 2) +
          (Real.exp (-(sharpConcreteDelta / 2)) - 1)) *
        (sharpConcreteRho d lambda * (m : ℝ))))
    (hslotRate : sharpConcreteZ d +
        2 * exponentialRowWeight (sharpConcreteZ d) *
          (isolatedLowerNeighborBudget (slotSupportBudget d) R d : ℝ) ≤
      sharpConcreteSlotGap d
          (OriginalIterationState.fixedSlackPaddedSlotTarget
            sharpConcreteGamma d) lambda ^ 2 /
        (4 * sharpConcreteSlotMean d
          (OriginalIterationState.fixedSlackPaddedSlotTarget
            sharpConcreteGamma d) lambda))
    (hupperRate : sharpConcreteZ d + Real.log 2 ≤
      sharpConcreteJobGap d
          (OriginalIterationState.fixedSlackPaddedSlotTarget
            sharpConcreteGamma d) lambda ^ 2 /
        (4 * sharpConcreteJobMean d
          (OriginalIterationState.fixedSlackPaddedSlotTarget
            sharpConcreteGamma d) lambda))
    (hupperProduct : exponentialRowWeight (sharpConcreteZ d) *
      (increasingNeighborBudget (upperSupportBudget d) R d : ℝ) ≤ 1 / 2)
    (hgroupLossEnvelope :
      isolatedRowConflictWeightedMomentEnvelope
          (sharpConcreteRho d lambda) (K * d) (3 * d)
            (sharpConcreteMomentOrder d) ≤
        ((sharpConcreteDelta / 2) * sharpConcreteRho d lambda * m) / 2)
    (hgroupLossProduct : exponentialRowWeight (sharpConcreteZ d) *
      (increasingNeighborBudget
        (isolatedConflictSupportBudget (groupSupportBudget K d) d) R d : ℝ) ≤
        1 / 2)
    (hslotLossProduct : exponentialRowWeight (sharpConcreteZ d) *
      (increasingNeighborBudget
        (isolatedConflictSupportBudget (slotSupportBudget d) d) R d : ℝ) ≤
        1 / 2)
    (hcollisionProduct : exponentialRowWeight (sharpConcreteZ d) *
      (increasingNeighborBudget (slotSupportBudget d) R d : ℝ) ≤ 1 / 2)
    (hIsolationBudget :
      18 * sharpScaledA lambda ^ 2 * d +
          72 * sharpScaledA lambda * sharpConcreteMomentOrder d * lambda +
          24 * sharpConcreteMomentOrder d ^ 2 * lambda ≤
        sharpScaledEta lambda * d) :
    ∃ A : Finset Option,
      H.IsPartialMatching A ∧
      (∀ g, (1 - sharpConcreteDelta) *
          (sharpScaledA lambda / (d : ℝ)) * m <
        ∑ o ∈ A, H.jobGroupCoverageWeight members g o) ∧
      (∀ j, ¬ H.Covers A j →
        (WeightedEdgeColoring.fixedSlackJobRetention (sharpScaledA lambda)
            sharpConcreteGamma - sharpScaledEta lambda) * d ≤
          H.residualJobDegree A j) ∧
      (∀ s, (∀ p ∈ A, s ∉ H.slots p) →
        (H.residualSlotDegree A s : ℝ) ≤
          (WeightedEdgeColoring.fixedSlackSlotRetention (sharpScaledA lambda)
              sharpConcreteGamma * (1 - sharpConcreteGamma) +
            2 * sharpScaledEta lambda + sharpScaledEta lambda) * d) := by
  let S := OriginalIterationState.fixedSlackPaddedSlotTarget
    sharpConcreteGamma d
  let rho := sharpConcreteRho d lambda
  let a := sharpScaledA lambda
  let eta := sharpScaledEta lambda
  let k := sharpConcreteMomentOrder d
  let z := sharpConcreteZ d
  have hconst := sharpScaled_constants lambda hlambda
  have hrho := sharpScaled_rho_bounds lambda d hlambda hd
  have hrhoEq : rho = a / (d : ℝ) := rfl
  have hrhoPos : 0 < rho := by
    dsimp [rho, sharpConcreteRho, a]
    exact div_pos hconst.1 (by exact_mod_cast hd)
  have hs := sharpConcrete_paddedSlotChernoffData d lambda hlambda hscale
  have hj := sharpConcrete_paddedJobChernoffData d lambda hlambda hscale
  let slotTilt := sharpConcreteSlotTilt d S lambda
  let jobTilt := sharpConcreteJobTilt d S lambda
  have hslotTilt0 : 0 ≤ slotTilt := by
    dsimp [slotTilt, sharpConcreteSlotTilt]
    exact div_nonneg hs.2.1 (mul_nonneg (by norm_num) hs.1.le)
  have hjobTilt0 : 0 ≤ jobTilt := by
    dsimp [jobTilt, sharpConcreteJobTilt]
    exact div_nonneg hj.2.1 (mul_nonneg (by norm_num) hj.1.le)
  have hgroupExponent :
      Real.exp
          (((sharpConcreteDelta / 2) * (1 - sharpConcreteDelta / 2) +
              (Real.exp (-(sharpConcreteDelta / 2)) - 1)) *
            (rho * (m : ℝ))) ≤
        Real.exp (-(z + 2 * exponentialRowWeight z *
          (isolatedLowerNeighborBudget (groupSupportBudget K d) R d : ℝ))) := by
    apply Real.exp_le_exp.mpr
    dsimp [rho, z]
    linarith
  have hslotExponent : ∀ s : H.ActiveSlot 0,
      Real.exp (slotTilt *
          (((a * (2 - sharpConcreteGamma) * (1 - sharpConcreteGamma) -
              2 * eta) * d / (3 * lambda : ℕ)) +
            eta * d / (3 * lambda : ℕ)) +
        (Real.exp (-slotTilt) - 1) *
          linearRowMean (fun _ : Option ↦ rho)
            (H.residualDeleteWeight lambda) (Sum.inr s.1)) ≤
        Real.exp (-(z + 2 * exponentialRowWeight z *
          (isolatedLowerNeighborBudget (slotSupportBudget d) R d : ℝ))) := by
    intro s
    have hmean := H.residualDeleteWeight_slot_mean_ge_regular
      rho s.1 d S lambda hlambda hrho.1 htwo hjob hslot hjobSlot hslotPair
    have hmean' : sharpConcreteSlotMean d S lambda ≤
        linearRowMean (fun _ : Option ↦ rho)
          (H.residualDeleteWeight lambda) (Sum.inr s.1) := by
      simpa [sharpConcreteSlotMean, rho, sharpConcreteRho] using hmean
    have hchernoff := lower_chernoff_scalar_le
      (sharpConcreteSlotMean d S lambda)
      (sharpConcreteSlotGap d S lambda) hs.1 hs.2.1 hs.2.2
    have htarget :
        ((a * (2 - sharpConcreteGamma) * (1 - sharpConcreteGamma) -
            2 * eta) * d / (3 * lambda : ℕ)) +
          eta * d / (3 * lambda : ℕ) =
        sharpConcreteSlotMean d S lambda -
          sharpConcreteSlotGap d S lambda := by
      dsimp [sharpConcreteSlotGap, sharpConcreteSlotTarget, a, eta]
      ring
    have htilt : slotTilt = sharpConcreteSlotGap d S lambda /
        (2 * sharpConcreteSlotMean d S lambda) := by rfl
    have hpays := exp_neg_quadratic_pays
      (sharpConcreteSlotGap d S lambda ^ 2 /
        (4 * sharpConcreteSlotMean d S lambda)) z
      (2 * exponentialRowWeight z *
        (isolatedLowerNeighborBudget (slotSupportBudget d) R d : ℝ)) hslotRate
    have hpays' :
        Real.exp (-(sharpConcreteSlotGap d S lambda ^ 2) /
            (4 * sharpConcreteSlotMean d S lambda)) ≤
          Real.exp (-(z + 2 * exponentialRowWeight z *
            (isolatedLowerNeighborBudget (slotSupportBudget d) R d : ℝ))) := by
      convert hpays using 1 <;> ring
    have hbaseline := hchernoff.trans hpays'
    rw [← htarget, ← htilt] at hbaseline
    have hcoef : Real.exp (-slotTilt) - 1 ≤ 0 := by
      exact sub_nonpos.mpr
        (Real.exp_le_one_iff.mpr (neg_nonpos.mpr hslotTilt0))
    apply (Real.exp_le_exp.mpr ?_).trans hbaseline
    have hmul := mul_le_mul_of_nonpos_left hmean' hcoef
    convert add_le_add_right hmul
      (slotTilt *
        (((a * (2 - sharpConcreteGamma) * (1 - sharpConcreteGamma) -
          2 * eta) * d / (3 * lambda : ℕ)) +
          eta * d / (3 * lambda : ℕ))) using 1 <;> ring
  have hupperTail : ∀ j,
      Real.exp (-jobTilt *
          ((2 * a * (1 - sharpConcreteGamma) + eta) * d /
            (2 * lambda : ℕ)) +
        (Real.exp jobTilt - 1) *
          linearRowMean (fun _ : Option ↦ rho)
            (H.residualDeleteWeight lambda) (Sum.inl j)) ≤
        exponentialRowWeight z / 2 := by
    intro j
    have hslotLe : ∀ s, H.slotDegree s ≤ S := fun s ↦ (hslot s).le
    have hmean := H.residualDeleteWeight_job_mean_le_degree
      rho lambda S hlambda hrho.1 j hslotLe
    have hjobCard : ((H.fiber j).card : ℝ) = d := by exact_mod_cast hjob j
    rw [hjobCard] at hmean
    have hmean' : linearRowMean (fun _ : Option ↦ rho)
        (H.residualDeleteWeight lambda) (Sum.inl j) ≤
          sharpConcreteJobMean d S lambda := by
      simpa [sharpConcreteJobMean, rho, sharpConcreteRho] using hmean
    have hchernoff := upper_chernoff_scalar_le
      (sharpConcreteJobMean d S lambda)
      (sharpConcreteJobGap d S lambda) hj.1 hj.2.1 hj.2.2
    have htarget :
        (2 * a * (1 - sharpConcreteGamma) + eta) * d /
            (2 * lambda : ℕ) =
          sharpConcreteJobMean d S lambda +
            sharpConcreteJobGap d S lambda := by
      simp [sharpConcreteJobGap, sharpConcreteJobTarget, a, eta]
    have htilt : jobTilt = sharpConcreteJobGap d S lambda /
        (2 * sharpConcreteJobMean d S lambda) := by rfl
    have hbaseline :
        Real.exp (-jobTilt *
            (sharpConcreteJobMean d S lambda + sharpConcreteJobGap d S lambda) +
          (Real.exp jobTilt - 1) * sharpConcreteJobMean d S lambda) ≤
          exponentialRowWeight z / 2 := by
      rw [htilt]
      calc
        Real.exp (-(sharpConcreteJobGap d S lambda /
              (2 * sharpConcreteJobMean d S lambda)) *
              (sharpConcreteJobMean d S lambda +
                sharpConcreteJobGap d S lambda) +
            (Real.exp (sharpConcreteJobGap d S lambda /
              (2 * sharpConcreteJobMean d S lambda)) - 1) *
                sharpConcreteJobMean d S lambda) ≤
          Real.exp (-(sharpConcreteJobGap d S lambda ^ 2) /
            (4 * sharpConcreteJobMean d S lambda)) := hchernoff
        _ ≤ Real.exp (-(z + Real.log 2)) :=
          by simpa [S, neg_div] using
            (exp_neg_quadratic_pays _ z (Real.log 2) hupperRate)
        _ = exponentialRowWeight z / 2 := by
          rw [show -(z + Real.log 2) = -z - Real.log 2 by ring,
            Real.exp_sub, Real.exp_log (by norm_num : (0 : ℝ) < 2)]
          rfl
    rw [← htarget] at hbaseline
    have hcoef : 0 ≤ Real.exp jobTilt - 1 := by
      exact sub_nonneg.mpr (Real.one_le_exp hjobTilt0)
    apply (Real.exp_le_exp.mpr ?_).trans hbaseline
    have hmul := mul_le_mul_of_nonneg_left hmean' hcoef
    convert add_le_add_right hmul
      (-jobTilt * ((2 * a * (1 - sharpConcreteGamma) + eta) * d /
        (2 * lambda : ℕ))) using 1 <;> ring
  have hslotLossEnvelope :
      isolatedRowConflictWeightedMomentEnvelope rho
          ((d : ℝ) ^ 2 / lambda) (3 * d) k ≤
        (eta * d / (3 * lambda : ℕ)) / 2 := by
    exact isolatedSlotWeightedEnvelope_le_half a eta d lambda k hd hlambda
      hconst.1.le hIsolationBudget
  have hcollisionCorrection :
      36 * a * k * lambda + 12 * k ^ 2 * lambda ≤ eta * d / 2 :=
    collisionCorrection_of_isolationBudget a eta d lambda k hconst.1.le
      hIsolationBudget
  have hcollisionEnvelope :
      slotCollisionMomentEnvelope rho d d lambda k ≤ eta * d := by
    exact slotCollisionMomentEnvelope_uniform_le_of_split
      a eta d lambda k hd hconst.2.2.2.2.2 hcollisionCorrection
  have hjobInitial : ∀ j, d ≤ H.residualJobDegree ∅ j := by
    intro j
    rw [H.residualJobDegree_empty, hjob j]
  have hslotInitial : ∀ s,
      (H.residualSlotDegree ∅ s : ℝ) ≤
        (1 - sharpConcreteGamma) * d := by
    intro s
    rw [H.residualSlotDegree_empty, hslot s]
    exact Nat.floor_le (mul_nonneg
      (by norm_num [sharpConcreteGamma]) (Nat.cast_nonneg d))
  have hjobDegree : ∀ j, (H.fiber j).card ≤ d := fun j ↦ (hjob j).le
  have hslotDegree : ∀ s, H.slotDegree s ≤ d := by
    intro s
    rw [hslot s]
    exact OriginalIterationState.fixedSlackPaddedSlotTarget_le
      sharpConcreteGamma d (by norm_num [sharpConcreteGamma])
      (by norm_num [sharpConcreteGamma])
  simpa [rho, a, eta, k, z, S, sharpConcreteRho] using
    H.exists_isolatedSharpFixedSlackRound_uniformProposal members
      (fun _ ↦ slotTilt) (fun _ ↦ jobTilt)
      lambda d d R K m k rho a sharpConcreteGamma eta (2 * eta) eta eta
      z sharpConcreteDelta hlambda hrho.1 hrho.2.1 hrhoEq
      hjobInitial hslotInitial hjobDegree hslotDegree hjobSlot hslotPair
      hmembers hgroupSupportLower hgroupIncidence
      (by norm_num [sharpConcreteDelta])
      (by norm_num [sharpConcreteDelta]) hrhoPos hm hconst.2.1
      (fun _ ↦ hslotTilt0) (fun _ ↦ hjobTilt0)
      (sharpConcreteZ_pos d hd) hrowHalf hcollisionRow
      hgroupExponent hslotExponent hupperTail
      hupperProduct hgroupLossEnvelope hslotLossEnvelope
      hgroupLossProduct hslotLossProduct
      (sharpScaled_collisionThreshold_pos lambda d hlambda hd)
      hcollisionEnvelope hcollisionProduct

end WeightedEdgeColoring.RankThreeOptionSystem
