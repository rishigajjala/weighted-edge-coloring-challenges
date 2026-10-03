import WeightedEdgeColoring.RankThreeIsolatedVariableSlack
import WeightedEdgeColoring.RankThreeSharpChernoffScalar
import WeightedEdgeColoring.RankThreeSharpCollisionScalar

/-!
# A regular isolated round with variable fixed slack

This is the regular-system theorem used by the coefficient-one application.
It specializes the generic isolated Harris theorem to a uniform proposal,
but keeps the fixed application slack `gamma` as a parameter.
-/

namespace WeightedEdgeColoring.RankThreeOptionSystem

open scoped BigOperators
open WeightedEdgeColoring
open WeightedEdgeColoring.SharpFixedSlackNumeric

universe u v w x

variable {Job : Type u} {Slot : Type v} {Option : Type w} {Group : Type x}
  [Fintype Job] [Fintype Slot] [Fintype Option] [Fintype Group]
  [DecidableEq Job] [DecidableEq Slot] [DecidableEq Option] [DecidableEq Group]
  (H : RankThreeOptionSystem Job Slot Option)

private theorem variableSlackA_eighteen_sq_le_eta
    (alpha gamma : ℝ) (lambda : ℕ)
    (halpha0 : 0 < alpha) (halphaSmall : alpha ≤ 1 / 100000)
    (hgamma0 : 0 < gamma) (hlambda : 0 < lambda) :
    18 * variableSlackA alpha gamma lambda ^ 2 ≤
      variableSlackEta alpha gamma lambda := by
  have hlambdaR : (0 : ℝ) < lambda := by exact_mod_cast hlambda
  have hlambda1 : (1 : ℝ) ≤ lambda := by exact_mod_cast hlambda
  have ha0 : 0 ≤ variableSlackA alpha gamma lambda :=
    (variableSlackA_pos halpha0 hgamma0 hlambda).le
  have haBound : variableSlackA alpha gamma lambda ≤ gamma / 100000 := by
    unfold variableSlackA
    apply (div_le_iff₀ hlambdaR).2
    have hag := mul_le_mul_of_nonneg_right halphaSmall hgamma0.le
    have hg0 : 0 ≤ gamma / 100000 := by positivity
    calc
      alpha * gamma ≤ gamma / 100000 := by
        convert hag using 1 <;> ring
      _ ≤ gamma / 100000 * (lambda : ℝ) := by
        exact le_mul_of_one_le_right hg0 hlambda1
  have hsquare : variableSlackA alpha gamma lambda ^ 2 ≤
      variableSlackA alpha gamma lambda * (gamma / 100000) := by
    simpa [pow_two] using mul_le_mul_of_nonneg_left haBound ha0
  unfold variableSlackEta
  nlinarith

private theorem nat_le_of_cast_le_one_sub_mul
    (S d : ℕ) (gamma : ℝ) (hgamma0 : 0 < gamma)
    (hS : (S : ℝ) ≤ (1 - gamma) * d) : S ≤ d := by
  have hd0 : (0 : ℝ) ≤ d := by positivity
  have hone : 1 - gamma ≤ 1 := by linarith
  have hmul : (1 - gamma) * (d : ℝ) ≤ d := by
    simpa using mul_le_mul_of_nonneg_right hone hd0
  exact_mod_cast hS.trans hmul

/-- One isolated round on an exactly regular padded system, with arbitrary
fixed slack `gamma`.  All graph-dependent estimates are discharged.  The
remaining displayed inequalities are scalar Chernoff/Harris product costs.
-/
theorem exists_isolatedVariableSlackRound
    (members : Group → Finset Job)
    (alpha gamma delta z : ℝ) (lambda d S R K m k : ℕ)
    (halpha : 0 < alpha) (halphaSmall : alpha ≤ 1 / 100000)
    (hgamma0 : 0 < gamma) (hgammaHalf : gamma ≤ 1 / 2)
    (hdelta0 : 0 < delta) (hdelta1 : delta ≤ 1)
    (hd : 0 < d) (hlambda : 0 < lambda) (hm : 0 < m)
    (hSgap : (S : ℝ) ≤ (1 - gamma) * d)
    (htwo : ∀ o, (H.slots o).card = 2)
    (hjob : ∀ j, (H.fiber j).card = d)
    (hslot : ∀ s, H.slotDegree s = S)
    (hjobSlot : ∀ j s, H.jobSlotCodegree j s ≤ lambda)
    (hslotPair : ∀ s t, s ≠ t → H.slotPairCodegree s t ≤ lambda)
    (hmembers : ∀ g, (members g).card ≤ K)
    (hgroupSupportLower : ∀ g,
      m ≤ (linearRowSupport (H.jobGroupCoverageWeight members) g).card)
    (hgroupIncidence : ∀ j,
      ((Finset.univ : Finset Group).filter
        (fun g ↦ j ∈ members g)).card ≤ R)
    (hslotMean : 0 < variableSlackSlotMean alpha gamma d S lambda)
    (hslotGap0 : 0 ≤ variableSlackSlotGap alpha gamma d S lambda)
    (hslotGap2 : variableSlackSlotGap alpha gamma d S lambda ≤
      2 * variableSlackSlotMean alpha gamma d S lambda)
    (hjobMean : 0 < variableSlackJobMean alpha gamma d S lambda)
    (hjobGap0 : 0 ≤ variableSlackJobGap alpha gamma d S lambda)
    (hjobGap2 : variableSlackJobGap alpha gamma d S lambda ≤
      2 * variableSlackJobMean alpha gamma d S lambda)
    (hrowHalf : exponentialRowWeight z ≤ 1 / 2)
    (hcollisionRow : collisionWeight k ≤ exponentialRowWeight z)
    (hgroupRate : z + 2 * exponentialRowWeight z *
          (isolatedLowerNeighborBudget (groupSupportBudget K d) R d : ℝ) ≤
      -(((delta / 2) * (1 - delta / 2) +
          (Real.exp (-(delta / 2)) - 1)) *
        (variableSlackRho alpha gamma d lambda * (m : ℝ))))
    (hslotRate : z + 2 * exponentialRowWeight z *
          (isolatedLowerNeighborBudget (slotSupportBudget d) R d : ℝ) ≤
      variableSlackSlotGap alpha gamma d S lambda ^ 2 /
        (4 * variableSlackSlotMean alpha gamma d S lambda))
    (hupperRate : z + Real.log 2 ≤
      variableSlackJobGap alpha gamma d S lambda ^ 2 /
        (4 * variableSlackJobMean alpha gamma d S lambda))
    (hupperProduct : exponentialRowWeight z *
      (increasingNeighborBudget (upperSupportBudget d) R d : ℝ) ≤ 1 / 2)
    (hgroupLossEnvelope :
      isolatedRowConflictWeightedMomentEnvelope
          (variableSlackRho alpha gamma d lambda) (K * d) (3 * d) k ≤
        ((delta / 2) * variableSlackRho alpha gamma d lambda * m) / 2)
    (hgroupLossProduct : exponentialRowWeight z *
      (increasingNeighborBudget
        (isolatedConflictSupportBudget (groupSupportBudget K d) d) R d : ℝ) ≤
        1 / 2)
    (hslotLossProduct : exponentialRowWeight z *
      (increasingNeighborBudget
        (isolatedConflictSupportBudget (slotSupportBudget d) d) R d : ℝ) ≤
        1 / 2)
    (hcollisionProduct : exponentialRowWeight z *
      (increasingNeighborBudget (slotSupportBudget d) R d : ℝ) ≤ 1 / 2)
    (hIsolationBudget :
      18 * variableSlackA alpha gamma lambda ^ 2 * d +
          72 * variableSlackA alpha gamma lambda * k * lambda +
          24 * k ^ 2 * lambda ≤
        variableSlackEta alpha gamma lambda * d) :
    ∃ A : Finset Option,
      H.IsPartialMatching A ∧
      (∀ g, (1 - delta) * variableSlackRho alpha gamma d lambda * m <
        ∑ o ∈ A, H.jobGroupCoverageWeight members g o) ∧
      (∀ j, ¬ H.Covers A j →
        (WeightedEdgeColoring.fixedSlackJobRetention
            (variableSlackA alpha gamma lambda) gamma -
          variableSlackEta alpha gamma lambda) * d ≤
            H.residualJobDegree A j) ∧
      (∀ s, (∀ p ∈ A, s ∉ H.slots p) →
        (H.residualSlotDegree A s : ℝ) ≤
          (WeightedEdgeColoring.fixedSlackSlotRetention
              (variableSlackA alpha gamma lambda) gamma * (1 - gamma) +
            2 * variableSlackEta alpha gamma lambda +
            variableSlackEta alpha gamma lambda) * d) := by
  let a := variableSlackA alpha gamma lambda
  let eta := variableSlackEta alpha gamma lambda
  let rho := variableSlackRho alpha gamma d lambda
  let slotMean := variableSlackSlotMean alpha gamma d S lambda
  let slotGap := variableSlackSlotGap alpha gamma d S lambda
  let jobMean := variableSlackJobMean alpha gamma d S lambda
  let jobGap := variableSlackJobGap alpha gamma d S lambda
  let slotTilt := slotGap / (2 * slotMean)
  let jobTilt := jobGap / (2 * jobMean)
  have ha : 0 < a := variableSlackA_pos halpha hgamma0 hlambda
  have heta : 0 < eta := variableSlackEta_pos halpha hgamma0 hlambda
  have hrho : rho = a / (d : ℝ) := rfl
  have hrho0 : 0 ≤ rho := by
    rw [hrho]
    exact div_nonneg ha.le (by positivity)
  have hrho1 : rho ≤ 1 := by
    have hd1 : (1 : ℝ) ≤ d := by exact_mod_cast hd
    have hl1 : (1 : ℝ) ≤ lambda := by exact_mod_cast hlambda
    have ha1 : a ≤ 1 := by
      dsimp [a, variableSlackA]
      apply (div_le_iff₀ (show (0 : ℝ) < lambda by positivity)).2
      have hag := mul_le_mul halphaSmall hgammaHalf hgamma0.le
        (by norm_num : (0 : ℝ) ≤ 1 / 100000)
      have hl1 : (1 : ℝ) ≤ lambda := by exact_mod_cast hlambda
      nlinarith
    exact (div_le_one (show (0 : ℝ) < d by positivity)).2
      (ha1.trans hd1)
  have hrhoPos : 0 < rho := by
    rw [hrho]
    exact div_pos ha (by positivity)
  have hslotTilt0 : 0 ≤ slotTilt := by
    dsimp [slotTilt]
    positivity
  have hjobTilt0 : 0 ≤ jobTilt := by
    dsimp [jobTilt]
    positivity
  have hgroupExponent :
      Real.exp (((delta / 2) * (1 - delta / 2) +
          (Real.exp (-(delta / 2)) - 1)) * (rho * (m : ℝ))) ≤
        Real.exp (-(z + 2 * exponentialRowWeight z *
          (isolatedLowerNeighborBudget (groupSupportBudget K d) R d : ℝ))) := by
    apply Real.exp_le_exp.mpr
    linarith
  have hslotExponent : ∀ s : H.ActiveSlot 0,
      Real.exp (slotTilt *
          (((a * (2 - gamma) * (1 - gamma) - 2 * eta) * d /
              (3 * lambda : ℕ)) + eta * d / (3 * lambda : ℕ)) +
        (Real.exp (-slotTilt) - 1) *
          linearRowMean (fun _ : Option ↦ rho)
            (H.residualDeleteWeight lambda) (Sum.inr s.1)) ≤
        Real.exp (-(z + 2 * exponentialRowWeight z *
          (isolatedLowerNeighborBudget (slotSupportBudget d) R d : ℝ))) := by
    intro s
    have hmean := H.residualDeleteWeight_slot_mean_ge_regular
      rho s.1 d S lambda hlambda hrho0 htwo hjob hslot hjobSlot hslotPair
    have hmean' : slotMean ≤ linearRowMean (fun _ : Option ↦ rho)
        (H.residualDeleteWeight lambda) (Sum.inr s.1) := by
      simpa [slotMean, variableSlackSlotMean, rho,
        variableSlackRho] using hmean
    have hchernoff := lower_chernoff_scalar_le slotMean slotGap
      hslotMean hslotGap0 hslotGap2
    have htarget :
        ((a * (2 - gamma) * (1 - gamma) - 2 * eta) * d /
            (3 * lambda : ℕ)) + eta * d / (3 * lambda : ℕ) =
          slotMean - slotGap := by
      dsimp [slotMean, slotGap, variableSlackSlotGap,
        variableSlackSlotTarget, a, eta]
      ring
    have hpays :=
      exp_neg_quadratic_pays (slotGap ^ 2 / (4 * slotMean)) z
        (2 * exponentialRowWeight z *
          (isolatedLowerNeighborBudget (slotSupportBudget d) R d : ℝ))
        hslotRate
    have hpays' : Real.exp (-(slotGap ^ 2) / (4 * slotMean)) ≤
        Real.exp (-(z + 2 * exponentialRowWeight z *
          (isolatedLowerNeighborBudget (slotSupportBudget d) R d : ℝ))) := by
      simpa only [neg_div] using hpays
    have hbaseline := hchernoff.trans hpays'
    rw [← htarget] at hbaseline
    have hcoef : Real.exp (-slotTilt) - 1 ≤ 0 := by
      exact sub_nonpos.mpr
        (Real.exp_le_one_iff.mpr (neg_nonpos.mpr hslotTilt0))
    dsimp [slotTilt] at hcoef ⊢
    apply (Real.exp_le_exp.mpr ?_).trans hbaseline
    exact add_le_add le_rfl (mul_le_mul_of_nonpos_left hmean' hcoef)
  have hupperTail : ∀ j,
      Real.exp (-jobTilt *
          ((2 * a * (1 - gamma) + eta) * d / (2 * lambda : ℕ)) +
        (Real.exp jobTilt - 1) *
          linearRowMean (fun _ : Option ↦ rho)
            (H.residualDeleteWeight lambda) (Sum.inl j)) ≤
        exponentialRowWeight z / 2 := by
    intro j
    have hmean := H.residualDeleteWeight_job_mean_le_degree
      rho lambda S hlambda hrho0 j (fun s ↦ (hslot s).le)
    have hjobCard : ((H.fiber j).card : ℝ) = d := by exact_mod_cast hjob j
    rw [hjobCard] at hmean
    have hmean' : linearRowMean (fun _ : Option ↦ rho)
        (H.residualDeleteWeight lambda) (Sum.inl j) ≤ jobMean := by
      simpa [jobMean, variableSlackJobMean, rho,
        variableSlackRho] using hmean
    have hchernoff := upper_chernoff_scalar_le jobMean jobGap
      hjobMean hjobGap0 hjobGap2
    have htarget :
        (2 * a * (1 - gamma) + eta) * d / (2 * lambda : ℕ) =
          jobMean + jobGap := by
      simp [jobMean, jobGap, variableSlackJobGap,
        variableSlackJobTarget, a, eta]
    have hbaseline :
        Real.exp (-jobTilt * (jobMean + jobGap) +
            (Real.exp jobTilt - 1) * jobMean) ≤
          exponentialRowWeight z / 2 := by
      dsimp [jobTilt]
      calc
        Real.exp (-(jobGap / (2 * jobMean)) * (jobMean + jobGap) +
            (Real.exp (jobGap / (2 * jobMean)) - 1) * jobMean) ≤
          Real.exp (-(jobGap ^ 2) / (4 * jobMean)) := hchernoff
        _ ≤ Real.exp (-(z + Real.log 2)) := by
          have hpays := exp_neg_quadratic_pays
            (jobGap ^ 2 / (4 * jobMean)) z (Real.log 2) hupperRate
          simpa only [neg_div] using hpays
        _ = exponentialRowWeight z / 2 := by
          rw [show -(z + Real.log 2) = -z - Real.log 2 by ring,
            Real.exp_sub, Real.exp_log (by norm_num : (0 : ℝ) < 2)]
          rfl
    rw [← htarget] at hbaseline
    have hcoef : 0 ≤ Real.exp jobTilt - 1 := by
      exact sub_nonneg.mpr (Real.one_le_exp hjobTilt0)
    apply (Real.exp_le_exp.mpr ?_).trans hbaseline
    exact add_le_add le_rfl (mul_le_mul_of_nonneg_left hmean' hcoef)
  have hslotLossEnvelope :
      isolatedRowConflictWeightedMomentEnvelope rho
          ((d : ℝ) ^ 2 / lambda) (3 * d) k ≤
        (eta * d / (3 * lambda : ℕ)) / 2 := by
    exact isolatedSlotWeightedEnvelope_le_half a eta d lambda k hd hlambda
      ha.le hIsolationBudget
  have hcorrection :
      36 * a * k * lambda + 12 * k ^ 2 * lambda ≤ eta * d / 2 := by
    have hmean0 : 0 ≤ 18 * a ^ 2 * (d : ℝ) := by positivity
    have hrest :
        72 * a * (k : ℝ) * (lambda : ℝ) +
            24 * (k : ℝ) ^ 2 * (lambda : ℝ) ≤ eta * (d : ℝ) := by
      calc
        72 * a * (k : ℝ) * (lambda : ℝ) +
              24 * (k : ℝ) ^ 2 * (lambda : ℝ) ≤
            18 * a ^ 2 * (d : ℝ) +
              (72 * a * (k : ℝ) * (lambda : ℝ) +
                24 * (k : ℝ) ^ 2 * (lambda : ℝ)) :=
          le_add_of_nonneg_left hmean0
        _ = 18 * a ^ 2 * (d : ℝ) +
              72 * a * (k : ℝ) * (lambda : ℝ) +
                24 * (k : ℝ) ^ 2 * (lambda : ℝ) := by ring
        _ ≤ eta * (d : ℝ) := by simpa using hIsolationBudget
    calc
      36 * a * (k : ℝ) * (lambda : ℝ) +
          12 * (k : ℝ) ^ 2 * (lambda : ℝ) =
        (72 * a * (k : ℝ) * (lambda : ℝ) +
          24 * (k : ℝ) ^ 2 * (lambda : ℝ)) / 2 := by ring
      _ ≤ (eta * (d : ℝ)) / 2 :=
        div_le_div_of_nonneg_right hrest (by norm_num)
  have hmeanFits : 18 * a ^ 2 ≤ eta := by
    exact variableSlackA_eighteen_sq_le_eta alpha gamma lambda
      halpha halphaSmall hgamma0 hlambda
  have hcollisionEnvelope :
      slotCollisionMomentEnvelope rho d d lambda k ≤ eta * d := by
    simpa [rho, hrho] using
      (slotCollisionMomentEnvelope_uniform_le_of_split
        a eta d lambda k hd hmeanFits hcorrection)
  have hjobInitial : ∀ j, d ≤ H.residualJobDegree ∅ j := by
    intro j
    rw [H.residualJobDegree_empty, hjob j]
  have hslotInitial : ∀ s,
      (H.residualSlotDegree ∅ s : ℝ) ≤ (1 - gamma) * d := by
    intro s
    rw [H.residualSlotDegree_empty, hslot s]
    exact hSgap
  have hslotDegree : ∀ s, H.slotDegree s ≤ d := by
    intro s
    rw [hslot s]
    exact nat_le_of_cast_le_one_sub_mul S d gamma hgamma0 hSgap
  simpa [a, eta, rho, slotTilt, jobTilt] using
    H.exists_isolatedSharpFixedSlackRound_uniformProposal members
      (fun _ ↦ slotTilt) (fun _ ↦ jobTilt)
      lambda d d R K m k rho a gamma eta (2 * eta) eta eta z delta
      hlambda hrho0 hrho1 hrho
      hjobInitial hslotInitial (fun j ↦ (hjob j).le) hslotDegree
      hjobSlot hslotPair hmembers hgroupSupportLower hgroupIncidence
      hdelta0 hdelta1 hrhoPos hm heta
      (fun _ ↦ hslotTilt0) (fun _ ↦ hjobTilt0)
      (by
        have hz : 0 < z := by
          by_contra hn
          have : exponentialRowWeight z ≥ 1 := by
            unfold exponentialRowWeight
            exact Real.one_le_exp (by linarith)
          linarith
        exact hz)
      hrowHalf hcollisionRow hgroupExponent hslotExponent hupperTail
      hupperProduct hgroupLossEnvelope hslotLossEnvelope
      hgroupLossProduct hslotLossProduct
      (by positivity) hcollisionEnvelope hcollisionProduct

end WeightedEdgeColoring.RankThreeOptionSystem
