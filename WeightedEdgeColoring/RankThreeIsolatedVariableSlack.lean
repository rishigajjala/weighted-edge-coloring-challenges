import WeightedEdgeColoring.RankThreeIsolatedSharpScalar
import WeightedEdgeColoring.RankThreeIsolatedSharpUniform
import WeightedEdgeColoring.RankThreeOriginalTypeNaturalIteration

/-!
# Isolated rounds with a fixed, arbitrary slot slack

The coefficient-one application fixes a small accuracy parameter first and
then keeps a slot/job gap `gamma` throughout the nibble.  Thus `gamma` is a
positive constant during one application, but it cannot be hard-coded as
`1/4`.  This file records the scalar part of that substitution.

The proposal numerator is `alpha * gamma / lambda`.  Each of the job,
slot-isolation, and collision errors is
`alpha * gamma^2 / (64 * lambda)`; the direct slot-load error receives twice
that amount.  In particular the error is one order smaller in `gamma` than
the proposal.  This is exactly what preserves the same slot/job gap.
-/

namespace WeightedEdgeColoring

open RankThreeOptionSystem
open RankThreeOptionSystem.OriginalIterationState
open SharpFixedSlackNumeric

/-- Proposal numerator for a fixed positive gap `gamma`. -/
noncomputable def variableSlackA (alpha gamma : ℝ) (lambda : ℕ) : ℝ :=
  alpha * gamma / (lambda : ℝ)

/-- Each small error budget is one further factor `gamma` below the
proposal numerator. -/
noncomputable def variableSlackEta (alpha gamma : ℝ) (lambda : ℕ) : ℝ :=
  variableSlackA alpha gamma lambda * gamma / 64

theorem variableSlackA_pos
    {alpha gamma : ℝ} {lambda : ℕ}
    (halpha : 0 < alpha) (hgamma : 0 < gamma) (hlambda : 0 < lambda) :
    0 < variableSlackA alpha gamma lambda := by
  unfold variableSlackA
  positivity

theorem variableSlackEta_pos
    {alpha gamma : ℝ} {lambda : ℕ}
    (halpha : 0 < alpha) (hgamma : 0 < gamma) (hlambda : 0 < lambda) :
    0 < variableSlackEta alpha gamma lambda := by
  have ha := variableSlackA_pos halpha hgamma hlambda
  unfold variableSlackEta
  positivity

/-- The allocation `etaJob=etaIsolation=etaCollision=eta` and
`etaLoad=2*eta` preserves the same gap. -/
theorem variableSlack_error_fits
    {alpha gamma : ℝ} {lambda : ℕ}
    (halpha : 0 < alpha) (hgamma0 : 0 < gamma)
    (hgammaHalf : gamma ≤ 1 / 2) (hlambda : 0 < lambda) :
    (1 - gamma) * variableSlackEta alpha gamma lambda +
        2 * variableSlackEta alpha gamma lambda +
        variableSlackEta alpha gamma lambda ≤
      variableSlackA alpha gamma lambda * gamma * (1 - gamma) := by
  have ha := variableSlackA_pos halpha hgamma0 hlambda
  unfold variableSlackEta
  have hfactor : (1 - gamma) / 64 + 2 / 64 + 1 / 64 ≤ 1 - gamma := by
    nlinarith
  calc
    (1 - gamma) * (variableSlackA alpha gamma lambda * gamma / 64) +
          2 * (variableSlackA alpha gamma lambda * gamma / 64) +
          variableSlackA alpha gamma lambda * gamma / 64 =
        (variableSlackA alpha gamma lambda * gamma) *
          ((1 - gamma) / 64 + 2 / 64 + 1 / 64) := by ring
    _ ≤ (variableSlackA alpha gamma lambda * gamma) * (1 - gamma) :=
      mul_le_mul_of_nonneg_left hfactor (mul_nonneg ha.le hgamma0.le)
    _ = variableSlackA alpha gamma lambda * gamma * (1 - gamma) := by ring

theorem variableSlack_jobRetention_pos
    {alpha gamma : ℝ} {lambda : ℕ}
    (halpha : 0 < alpha) (hgamma0 : 0 < gamma)
    (hgammaHalf : gamma ≤ 1 / 2) (hlambda : 0 < lambda)
    (halphaSmall : alpha ≤ 1) :
    0 < fixedSlackJobRetention (variableSlackA alpha gamma lambda) gamma -
      variableSlackEta alpha gamma lambda := by
  have ha := variableSlackA_pos halpha hgamma0 hlambda
  have hlambdaR : (1 : ℝ) ≤ lambda := by exact_mod_cast hlambda
  have ha1 : variableSlackA alpha gamma lambda ≤ gamma := by
    unfold variableSlackA
    apply (div_le_iff₀ (show (0 : ℝ) < lambda by positivity)).2
    nlinarith
  unfold fixedSlackJobRetention variableSlackEta
  nlinarith

theorem variableSlack_slotRetention_pos
    {alpha gamma : ℝ} {lambda : ℕ}
    (halpha : 0 < alpha) (hgamma0 : 0 < gamma)
    (hgammaHalf : gamma ≤ 1 / 2) (hlambda : 0 < lambda)
    (halphaSmall : alpha ≤ 1) :
    0 < fixedSlackSlotRetention (variableSlackA alpha gamma lambda) gamma *
          (1 - gamma) +
        2 * variableSlackEta alpha gamma lambda +
        variableSlackEta alpha gamma lambda := by
  have ha := variableSlackA_pos halpha hgamma0 hlambda
  have hlambdaR : (1 : ℝ) ≤ lambda := by exact_mod_cast hlambda
  have ha1 : variableSlackA alpha gamma lambda ≤ gamma := by
    unfold variableSlackA
    apply (div_le_iff₀ (show (0 : ℝ) < lambda by positivity)).2
    nlinarith
  have hgamma1 : gamma ≤ 1 := hgammaHalf.trans (by norm_num)
  have htwo0 : 0 ≤ 2 - gamma := by linarith
  have hprod : variableSlackA alpha gamma lambda * (2 - gamma) ≤ 1 := by
    calc
      variableSlackA alpha gamma lambda * (2 - gamma) ≤
          gamma * (2 - gamma) := mul_le_mul_of_nonneg_right ha1 htwo0
      _ ≤ 1 := by nlinarith [sq_nonneg (gamma - 1)]
  have hret0 : 0 ≤ fixedSlackSlotRetention
      (variableSlackA alpha gamma lambda) gamma := by
    unfold fixedSlackSlotRetention
    linarith
  have hgap0 : 0 ≤ 1 - gamma := sub_nonneg.mpr hgamma1
  have heta := variableSlackEta_pos halpha hgamma0 hlambda
  unfold fixedSlackSlotRetention variableSlackEta
  nlinarith [mul_nonneg hret0 hgap0]

/-! ## The honest squared-codegree loss condition -/

/-- A parameter-only inequality implies the isolation moment budget after
the substitution `a=alpha*gamma/lambda`.  The scale hypothesis has the
necessary square on `lambda`.

This is deliberately stated with a free `beta0`.  Once `alpha` and `gamma`
are fixed, one chooses any positive `beta0` satisfying `hfixed`; the usual
`d/lambda^2 >> log(d)^2` estimate supplies `hratio`. -/
theorem variableSlack_isolationBudget_of_square_ratio
    (alpha gamma beta0 : ℝ) (d lambda : ℕ)
    (hd : 0 < d) (hlambda : 0 < lambda)
    (halpha : 0 ≤ alpha) (hgamma : 0 ≤ gamma) (hbeta0 : 0 ≤ beta0)
    (hratio : (lambda : ℝ) ^ 2 * sharpConcreteMomentUpper d ^ 2 ≤
      beta0 * d)
    (hfixed :
      18 * (alpha * gamma) ^ 2 +
          (72 * (alpha * gamma) + 24) * beta0 ≤
        alpha * gamma ^ 2 / 64) :
    18 * variableSlackA alpha gamma lambda ^ 2 * d +
        72 * variableSlackA alpha gamma lambda *
          sharpConcreteMomentOrder d * lambda +
        24 * sharpConcreteMomentOrder d ^ 2 * lambda ≤
      variableSlackEta alpha gamma lambda * d := by
  have hlambdaR : (0 : ℝ) < lambda := by exact_mod_cast hlambda
  have hratio' : (lambda : ℝ) * sharpConcreteMomentUpper d ^ 2 ≤
      (beta0 / lambda) * d := by
    rw [show (beta0 / (lambda : ℝ)) * d =
      (beta0 * d) / lambda by ring]
    apply (le_div_iff₀ hlambdaR).2
    calc
      (lambda : ℝ) * sharpConcreteMomentUpper d ^ 2 * lambda =
          (lambda : ℝ) ^ 2 * sharpConcreteMomentUpper d ^ 2 := by ring
      _ ≤ beta0 * d := hratio
  have hbudget :
      18 * ((alpha * gamma) / lambda) ^ 2 +
          (72 * ((alpha * gamma) / lambda) + 24) * (beta0 / lambda) ≤
        (alpha * gamma ^ 2 / 64) / lambda := by
    have hlambda1 : (1 : ℝ) ≤ lambda := by exact_mod_cast hlambda
    have hscaled := div_le_div_of_nonneg_right hfixed hlambdaR.le
    have hfirst :
        18 * ((alpha * gamma) / lambda) ^ 2 ≤
          (18 * (alpha * gamma) ^ 2) / lambda := by
      rw [div_pow]
      have hsq : (lambda : ℝ) ≤ lambda ^ 2 := by nlinarith
      have hnum : 0 ≤ 18 * (alpha * gamma) ^ 2 := by positivity
      convert div_le_div_of_nonneg_left hnum hlambdaR hsq using 1 <;> ring
    have hcoefficient :
        72 * ((alpha * gamma) / lambda) + 24 ≤
          72 * (alpha * gamma) + 24 := by
      have hag0 : 0 ≤ alpha * gamma := mul_nonneg halpha hgamma
      have hdiv : (alpha * gamma) / lambda ≤ alpha * gamma :=
        (div_le_iff₀ hlambdaR).2 (by nlinarith)
      nlinarith
    have hsecond :
        (72 * ((alpha * gamma) / lambda) + 24) * (beta0 / lambda) ≤
          ((72 * (alpha * gamma) + 24) * beta0) / lambda := by
      rw [mul_div_assoc]
      have h := div_le_div_of_nonneg_right
        (mul_le_mul_of_nonneg_right hcoefficient hbeta0) hlambdaR.le
      convert h using 1 <;> ring
    calc
      18 * ((alpha * gamma) / lambda) ^ 2 +
          (72 * ((alpha * gamma) / lambda) + 24) * (beta0 / lambda) ≤
        (18 * (alpha * gamma) ^ 2) / lambda +
          ((72 * (alpha * gamma) + 24) * beta0) / lambda :=
            add_le_add hfirst hsecond
      _ = (18 * (alpha * gamma) ^ 2 +
          (72 * (alpha * gamma) + 24) * beta0) / lambda := by ring
      _ ≤ (alpha * gamma ^ 2 / 64) / lambda := hscaled
  have hmain := isolatedLoss_scaled_of_square_ratio
    ((alpha * gamma) / lambda) ((alpha * gamma ^ 2 / 64) / lambda)
      (beta0 / lambda) d lambda hd hlambda (by positivity) (by positivity)
      hratio' hbudget
  convert hmain using 1 <;>
    simp only [variableSlackA, variableSlackEta] <;> ring

/-- A convenient positive choice for the squared-codegree coefficient.
It is much smaller than needed, which keeps the following arithmetic proof
independent of any delicate optimization. -/
noncomputable def variableSlackBeta0 (alpha gamma : ℝ) : ℝ :=
  alpha * gamma ^ 2 / 100000

theorem variableSlack_fixed_isolation_budget
    {alpha gamma : ℝ}
    (halpha0 : 0 < alpha) (halphaSmall : alpha ≤ 1 / 100000)
    (hgamma0 : 0 < gamma) (hgamma1 : gamma ≤ 1) :
    18 * (alpha * gamma) ^ 2 +
          (72 * (alpha * gamma) + 24) *
            variableSlackBeta0 alpha gamma ≤
        alpha * gamma ^ 2 / 64 := by
  unfold variableSlackBeta0
  have hag0 : 0 ≤ alpha * gamma := by positivity
  have hg2 : 0 ≤ gamma ^ 2 := sq_nonneg gamma
  have ha2 : alpha ^ 2 ≤ alpha / 100000 := by
    nlinarith [mul_le_mul_of_nonneg_left halphaSmall halpha0.le]
  have hag_le : alpha * gamma ≤ alpha := by
    nlinarith [mul_le_mul_of_nonneg_left hgamma1 halpha0.le]
  nlinarith [mul_nonneg halpha0.le hg2]

/-! ## Endpoint block loss -/

/-- The endpoint-block choice only needs to dominate
`lambda*k^2/(alpha*gamma*delta)`.  This form avoids rounding a constant
which is fixed only after the target accuracy is chosen. -/
theorem variableSlack_groupLossEnvelope_of_blockScale
    (alpha gamma delta : ℝ) (d lambda K k : ℕ)
    (hd : 0 < d) (hlambda : 0 < lambda) (hk : 0 < k)
    (halpha0 : 0 < alpha) (hgamma0 : 0 < gamma)
    (hdelta0 : 0 < delta) (hdelta1 : delta ≤ 1)
    (haSmall : variableSlackA alpha gamma lambda ≤ delta / 96)
    (hblock : 128 * (lambda : ℝ) * (k : ℝ) ^ 2 ≤
      delta * alpha * gamma * K) :
    isolatedRowConflictWeightedMomentEnvelope
        (variableSlackA alpha gamma lambda / (d : ℝ))
        ((2 * K : ℕ) * d) (3 * d) k ≤
      ((delta / 2) *
        (variableSlackA alpha gamma lambda / (d : ℝ)) *
          (K * d : ℕ)) / 2 := by
  have hdR : (0 : ℝ) < d := by exact_mod_cast hd
  have ha := variableSlackA_pos halpha0 hgamma0 hlambda
  have hk1 : (1 : ℝ) ≤ k := by exact_mod_cast hk
  have hkSq : (k : ℝ) ≤ k ^ 2 := by nlinarith
  have hidentity :
      isolatedRowConflictWeightedMomentEnvelope
          (variableSlackA alpha gamma lambda / (d : ℝ))
          ((2 * K : ℕ) * d) (3 * d) k =
        6 * variableSlackA alpha gamma lambda ^ 2 * K +
          12 * variableSlackA alpha gamma lambda * k + 4 * k ^ 2 := by
    unfold isolatedRowConflictWeightedMomentEnvelope
    push_cast
    field_simp
    ring
  rw [hidentity]
  have hblock' : 128 * (k : ℝ) ^ 2 ≤
      delta * variableSlackA alpha gamma lambda * K := by
    unfold variableSlackA
    have hlambdaR : (0 : ℝ) < lambda := by exact_mod_cast hlambda
    rw [show delta * (alpha * gamma / (lambda : ℝ)) * K =
      (delta * alpha * gamma * K) / (lambda : ℝ) by ring]
    apply (le_div_iff₀ hlambdaR).2
    convert hblock using 1 <;> ring
  have hquadratic : 16 * (k : ℝ) ^ 2 ≤
      delta * variableSlackA alpha gamma lambda * K / 8 := by
    linarith
  have hlinear : 12 * variableSlackA alpha gamma lambda * k ≤
      12 * k ^ 2 := by
    have ha1 : variableSlackA alpha gamma lambda ≤ 1 :=
      haSmall.trans (by nlinarith)
    nlinarith [mul_le_mul_of_nonneg_right ha1
      (show (0 : ℝ) ≤ k by positivity)]
  have hmean : 6 * variableSlackA alpha gamma lambda ^ 2 * K ≤
      delta * variableSlackA alpha gamma lambda * K / 16 := by
    have hK0 : (0 : ℝ) ≤ K := by positivity
    nlinarith [mul_le_mul_of_nonneg_right haSmall
      (mul_nonneg ha.le hK0)]
  have hrhs :
      ((delta / 2) *
          (variableSlackA alpha gamma lambda / (d : ℝ)) *
            ((K * d : ℕ) : ℝ)) / 2 =
        delta * variableSlackA alpha gamma lambda * K / 4 := by
    push_cast
    field_simp [hdR.ne']
    ring
  rw [hrhs]
  nlinarith

/-! ## Eventual closure on the `N=n^(3/2)` scale -/

/-- For fixed positive `alpha,gamma`, the honest isolation condition follows
on the cube/square scale: `lambda≤r`, `r^3≤d`, and polynomial upper growth
of `d`. -/
theorem eventually_variableSlack_square_ratio_cube_scale
    (alpha gamma : ℝ) (C : ℕ)
    (halpha : 0 < alpha) (hgamma : 0 < gamma) :
    ∀ᶠ r : ℕ in Filter.atTop, ∀ d lambda : ℕ,
      0 < d → 0 < r → lambda ≤ r → r ^ 3 ≤ d →
      d ≤ (r + 1) ^ C →
      (lambda : ℝ) ^ 2 * sharpConcreteMomentUpper d ^ 2 ≤
        variableSlackBeta0 alpha gamma * d := by
  have hbeta : 0 < variableSlackBeta0 alpha gamma := by
    unfold variableSlackBeta0
    positivity
  have hB0 : (0 : ℝ) ≤ 8 * (C : ℝ) + 10 := by positivity
  filter_upwards [eventually_mul_log_sq_le_linear
      (8 * (C : ℝ) + 10) (variableSlackBeta0 alpha gamma) hB0 hbeta,
      Filter.eventually_ge_atTop (1 : ℕ)] with r hsquare hr
  intro d lambda hd _hr hlambda hdlower hdupper
  have hU := sharpConcreteMomentUpper_le_of_polynomial_growth d r C hr hdupper
  have hU0 : 0 ≤ sharpConcreteMomentUpper d :=
    le_trans (by norm_num) (sharpConcreteMomentUpper_one_le d hd)
  have hUsq : sharpConcreteMomentUpper d ^ 2 ≤
      ((8 * (C : ℝ) + 10) * Real.log ((r : ℝ) + 1)) ^ 2 :=
    pow_le_pow_left₀ hU0 hU 2
  have hlambdaR : (lambda : ℝ) ≤ r := by exact_mod_cast hlambda
  have hlambdaSq : (lambda : ℝ) ^ 2 ≤ r ^ 2 :=
    pow_le_pow_left₀ (by positivity) hlambdaR 2
  have hdlowerR : (r : ℝ) ^ 3 ≤ d := by exact_mod_cast hdlower
  calc
    (lambda : ℝ) ^ 2 * sharpConcreteMomentUpper d ^ 2 ≤
        r ^ 2 *
          ((8 * (C : ℝ) + 10) * Real.log ((r : ℝ) + 1)) ^ 2 := by
      gcongr
    _ ≤ r ^ 2 * (variableSlackBeta0 alpha gamma * r) := by gcongr
    _ = variableSlackBeta0 alpha gamma * r ^ 3 := by ring
    _ ≤ variableSlackBeta0 alpha gamma * d :=
      mul_le_mul_of_nonneg_left hdlowerR hbeta.le

/-- Exact scalar names for the variable-gap Chernoff rows.  These are the
quantities to be bounded in the selected-profile application. -/
noncomputable def variableSlackRho (alpha gamma : ℝ) (d lambda : ℕ) : ℝ :=
  variableSlackA alpha gamma lambda / (d : ℝ)

noncomputable def variableSlackSlotMean
    (alpha gamma : ℝ) (d S lambda : ℕ) : ℝ :=
  variableSlackRho alpha gamma d lambda *
    (((S * (d + S - 3 * lambda) : ℕ) : ℝ) /
      ((3 * lambda : ℕ) : ℝ))

noncomputable def variableSlackSlotTarget
    (alpha gamma : ℝ) (d lambda : ℕ) : ℝ :=
  (variableSlackA alpha gamma lambda * (2 - gamma) * (1 - gamma) -
      variableSlackEta alpha gamma lambda) * d /
    (3 * lambda : ℕ)

noncomputable def variableSlackSlotGap
    (alpha gamma : ℝ) (d S lambda : ℕ) : ℝ :=
  variableSlackSlotMean alpha gamma d S lambda -
    variableSlackSlotTarget alpha gamma d lambda

noncomputable def variableSlackJobMean
    (alpha gamma : ℝ) (d S lambda : ℕ) : ℝ :=
  variableSlackRho alpha gamma d lambda *
    ((d : ℝ) * (S : ℝ) / (lambda : ℝ))

noncomputable def variableSlackJobTarget
    (alpha gamma : ℝ) (d lambda : ℕ) : ℝ :=
  (2 * variableSlackA alpha gamma lambda * (1 - gamma) +
      variableSlackEta alpha gamma lambda) * d /
    (2 * lambda : ℕ)

noncomputable def variableSlackJobGap
    (alpha gamma : ℝ) (d S lambda : ℕ) : ℝ :=
  variableSlackJobTarget alpha gamma d lambda -
    variableSlackJobMean alpha gamma d S lambda

/-- The upper job row has a clean gap: padding the slot degree below
`(1-gamma)d` leaves half of the allocated job error as Chernoff room. -/
theorem variableSlackJobGap_lower
    {alpha gamma : ℝ} {d S lambda : ℕ}
    (halpha : 0 < alpha) (hgamma : 0 < gamma)
    (hd : 0 < d) (hlambda : 0 < lambda)
    (hS : (S : ℝ) ≤ (1 - gamma) * d) :
    variableSlackEta alpha gamma lambda * d / (2 * lambda : ℕ) ≤
      variableSlackJobGap alpha gamma d S lambda := by
  have hdR : (0 : ℝ) < d := by exact_mod_cast hd
  have hlambdaR : (0 : ℝ) < lambda := by exact_mod_cast hlambda
  have ha := variableSlackA_pos halpha hgamma hlambda
  have hprod := mul_le_mul_of_nonneg_left hS ha.le
  have hprodScaled := mul_le_mul_of_nonneg_right hprod
    (show (0 : ℝ) ≤ 2 * (lambda : ℝ) by positivity)
  unfold variableSlackJobGap variableSlackJobTarget
    variableSlackJobMean variableSlackRho
  field_simp [hdR.ne', hlambdaR.ne']
  push_cast
  nlinarith [hprodScaled]

/-- The regular lower slot row also has linear gap.  The loss caused by the
floor and by the `3*lambda` codegree correction is absorbed once
`gamma*d` dominates `lambda+1`.  The constant is intentionally loose. -/
theorem variableSlackSlotGap_lower
    {alpha gamma : ℝ} {d S lambda : ℕ}
    (halpha : 0 < alpha) (hgamma0 : 0 < gamma)
    (hgammaHalf : gamma ≤ 1 / 2)
    (hd : 0 < d) (hlambda : 0 < lambda)
    (hSlower : (1 - gamma) * d - 1 ≤ (S : ℝ))
    (hscale : 1000 * ((lambda : ℝ) + 1) ≤ gamma * d) :
    variableSlackEta alpha gamma lambda * d / (6 * lambda : ℕ) ≤
      variableSlackSlotGap alpha gamma d S lambda := by
  have hdR : (0 : ℝ) < d := by exact_mod_cast hd
  have hlambdaR : (0 : ℝ) < lambda := by exact_mod_cast hlambda
  have ha := variableSlackA_pos halpha hgamma0 hlambda
  have hx0 : 0 ≤ 1 - gamma := by linarith
  have hdLarge : (6 : ℝ) ≤ d := by
    have hlambda1 : (1 : ℝ) ≤ lambda := by exact_mod_cast hlambda
    nlinarith
  have hfirst0 : 0 ≤ (1 - gamma) * d - 1 := by
    nlinarith
  have hsecondLower :
      (2 - gamma) * d - 1 - 3 * lambda ≤
        (d : ℝ) + S - 3 * lambda := by
    nlinarith
  have hsecond0 : 0 ≤ (2 - gamma) * d - 1 - 3 * lambda := by
    have hlambda1 : (1 : ℝ) ≤ lambda := by exact_mod_cast hlambda
    nlinarith
  have hsub : 3 * lambda ≤ d + S := by
    have hsubR : ((3 * lambda : ℕ) : ℝ) ≤ ((d + S : ℕ) : ℝ) := by
      push_cast
      nlinarith [hsecondLower, hsecond0]
    exact_mod_cast hsubR
  have hproduct :
      ((1 - gamma) * d - 1) *
          ((2 - gamma) * d - 1 - 3 * lambda) ≤
        (S : ℝ) * ((d : ℝ) + S - 3 * lambda) := by
    exact mul_le_mul hSlower hsecondLower hsecond0
      (Nat.cast_nonneg S)
  have hbracket :
      (1 - gamma) * (2 - gamma) * d -
          ((1 - gamma) * (1 + 3 * lambda) + (2 - gamma)) ≤
        (S : ℝ) * ((d : ℝ) + S - 3 * lambda) / d := by
    apply (le_div_iff₀ hdR).2
    nlinarith [hproduct]
  have hroom :
      (1 - gamma) * (1 + 3 * lambda) + (2 - gamma) +
          gamma * d / 384 ≤ gamma * d / 64 := by
    have hlambda1 : (1 : ℝ) ≤ lambda := by exact_mod_cast hlambda
    nlinarith
  have hnormalized :
      (1 - gamma) * (2 - gamma) * d + gamma * d / 384 ≤
        (S : ℝ) * ((d : ℝ) + S - 3 * lambda) / d +
          gamma * d / 64 := by
    linarith
  unfold variableSlackSlotGap variableSlackSlotMean
    variableSlackSlotTarget variableSlackRho variableSlackEta
  have hpositiveScale :
      0 < variableSlackA alpha gamma lambda / (3 * (lambda : ℝ)) := by
    positivity
  calc
    (variableSlackA alpha gamma lambda * gamma / 64) * d /
          (((6 * lambda : ℕ) : ℝ)) =
        (variableSlackA alpha gamma lambda / (3 * (lambda : ℝ))) *
          (gamma * d / 128) := by
            push_cast
            ring
    _ ≤ (variableSlackA alpha gamma lambda / (3 * (lambda : ℝ))) *
        ((S : ℝ) * ((d : ℝ) + S - 3 * lambda) / d -
          (1 - gamma) * (2 - gamma) * d + gamma * d / 64) := by
            apply mul_le_mul_of_nonneg_left _ hpositiveScale.le
            nlinarith
    _ = variableSlackA alpha gamma lambda / (d : ℝ) *
          (((S * (d + S - 3 * lambda) : ℕ) : ℝ) /
            ((3 * lambda : ℕ) : ℝ)) -
        (variableSlackA alpha gamma lambda * (2 - gamma) *
            (1 - gamma) -
          (variableSlackA alpha gamma lambda * gamma / 64)) * d /
            ((3 * lambda : ℕ) : ℝ) := by
              rw [Nat.cast_mul, Nat.cast_sub hsub]
              push_cast
              field_simp [hdR.ne', hlambdaR.ne']
              ring

end WeightedEdgeColoring
