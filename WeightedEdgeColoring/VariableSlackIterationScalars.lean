import WeightedEdgeColoring.RankThreeIsolatedVariableSlack

/-!
# Elementary iteration inequalities for the variable-slack parameters

These bounds expose the exact `1-O(1/lambda)` job retention used by the
outer simple-graph iteration.
-/

namespace WeightedEdgeColoring

noncomputable section

/-- The one-round job retention is at most one. -/
theorem variableSlack_jobRetention_le_one
    {alpha gamma : ℝ} {lambda : ℕ}
    (halpha : 0 ≤ alpha) (hgamma0 : 0 ≤ gamma)
    (hgamma1 : gamma ≤ 1) (hlambda : 0 < lambda) :
    fixedSlackJobRetention (variableSlackA alpha gamma lambda) gamma -
        variableSlackEta alpha gamma lambda ≤ 1 := by
  have ha0 : 0 ≤ variableSlackA alpha gamma lambda := by
    unfold variableSlackA
    positivity
  have heta0 : 0 ≤ variableSlackEta alpha gamma lambda := by
    unfold variableSlackEta
    positivity
  unfold fixedSlackJobRetention
  nlinarith [mul_nonneg ha0 (sub_nonneg.mpr hgamma1)]

/-- The lost fraction in one job recurrence step is at most `3a`. -/
theorem variableSlack_jobDecay_le_threeA
    {alpha gamma : ℝ} {lambda : ℕ}
    (halpha : 0 ≤ alpha) (hgamma0 : 0 ≤ gamma)
    (hgamma1 : gamma ≤ 1) (hlambda : 0 < lambda) :
    1 - (fixedSlackJobRetention (variableSlackA alpha gamma lambda) gamma -
        variableSlackEta alpha gamma lambda) ≤
      3 * variableSlackA alpha gamma lambda := by
  have ha0 : 0 ≤ variableSlackA alpha gamma lambda := by
    unfold variableSlackA
    positivity
  unfold fixedSlackJobRetention variableSlackEta
  nlinarith [mul_nonneg ha0 (sub_nonneg.mpr hgamma1)]

/-- With the manuscript's small proposal constant, job retention is at
least one half. -/
theorem variableSlack_half_le_jobRetention
    {alpha gamma : ℝ} {lambda : ℕ}
    (halpha : 0 ≤ alpha) (halphaSmall : alpha ≤ 1 / 6)
    (hgamma0 : 0 ≤ gamma) (hgamma1 : gamma ≤ 1)
    (hlambda : 0 < lambda) :
    1 / 2 ≤
      fixedSlackJobRetention (variableSlackA alpha gamma lambda) gamma -
        variableSlackEta alpha gamma lambda := by
  have hlambdaR : (1 : ℝ) ≤ lambda := by exact_mod_cast hlambda
  have hagamma : alpha * gamma ≤ alpha := by
    nlinarith [mul_le_mul_of_nonneg_left hgamma1 halpha]
  have ha : variableSlackA alpha gamma lambda ≤ alpha := by
    unfold variableSlackA
    apply (div_le_iff₀ (show (0 : ℝ) < lambda by positivity)).2
    nlinarith
  have hdecay := variableSlack_jobDecay_le_threeA
    halpha hgamma0 hgamma1 hlambda
  nlinarith

/-- If the number of rounds is at most `T*lambda`, the total exponent in
the recurrence is at most `3*alpha*gamma*T`. -/
theorem variableSlack_jobDecay_mul_steps_le
    {alpha gamma T : ℝ} {lambda steps : ℕ}
    (halpha : 0 ≤ alpha) (hgamma0 : 0 ≤ gamma)
    (hgamma1 : gamma ≤ 1) (hlambda : 0 < lambda)
    (hsteps : (steps : ℝ) ≤ T * lambda) :
    (1 - (fixedSlackJobRetention (variableSlackA alpha gamma lambda) gamma -
        variableSlackEta alpha gamma lambda)) * steps ≤
      3 * alpha * gamma * T := by
  have hdecay := variableSlack_jobDecay_le_threeA
    halpha hgamma0 hgamma1 hlambda
  have ha0 : 0 ≤ variableSlackA alpha gamma lambda := by
    unfold variableSlackA
    positivity
  have heta0 : 0 ≤ variableSlackEta alpha gamma lambda := by
    unfold variableSlackEta
    positivity
  have hdecay0 : 0 ≤
      1 - (fixedSlackJobRetention (variableSlackA alpha gamma lambda) gamma -
        variableSlackEta alpha gamma lambda) := by
    unfold fixedSlackJobRetention variableSlackEta
    nlinarith [mul_nonneg ha0 (sub_nonneg.mpr hgamma1)]
  have hlambdaR : (0 : ℝ) < lambda := by exact_mod_cast hlambda
  calc
    (1 - (fixedSlackJobRetention (variableSlackA alpha gamma lambda) gamma -
        variableSlackEta alpha gamma lambda)) * steps ≤
        (3 * variableSlackA alpha gamma lambda) * steps :=
      mul_le_mul_of_nonneg_right hdecay (Nat.cast_nonneg steps)
    _ ≤ (3 * variableSlackA alpha gamma lambda) * (T * lambda) :=
      mul_le_mul_of_nonneg_left hsteps
        (mul_nonneg (by norm_num) ha0)
    _ = 3 * alpha * gamma * T := by
      unfold variableSlackA
      field_simp [hlambdaR.ne'] <;> ring

/-- The exact gap coefficient in the integer recurrence keeps a fixed
quarter of its leading `a*gamma` term. -/
theorem variableSlack_marginCoefficient_lower
    {alpha gamma : ℝ} {lambda : ℕ}
    (halpha : 0 ≤ alpha) (hgamma0 : 0 ≤ gamma)
    (hgammaHalf : gamma ≤ 1 / 2) (hlambda : 0 < lambda) :
    variableSlackA alpha gamma lambda * gamma * (1 - gamma) -
        ((1 - gamma) * variableSlackEta alpha gamma lambda +
          3 * variableSlackEta alpha gamma lambda) ≥
      variableSlackA alpha gamma lambda * gamma / 4 := by
  have ha0 : 0 ≤ variableSlackA alpha gamma lambda := by
    unfold variableSlackA
    positivity
  have hfactor : (1 / 4 : ℝ) ≤
      (1 - gamma) - ((1 - gamma) + 3) / 64 := by
    nlinarith
  have hmul := mul_le_mul_of_nonneg_left hfactor
    (mul_nonneg ha0 hgamma0)
  unfold variableSlackEta
  nlinarith

/-- A transparent degree condition implies the rounded slot/job margin
hypothesis used in every round. -/
theorem variableSlack_iterationMargin_of_degree
    {alpha gamma : ℝ} {lambda d : ℕ}
    (halpha : 0 ≤ alpha) (hgamma0 : 0 ≤ gamma)
    (hgammaHalf : gamma ≤ 1 / 2) (hlambda : 0 < lambda)
    (hdegree : 4 * (1 - gamma) ≤
      variableSlackA alpha gamma lambda * gamma * d) :
    1 - gamma ≤
      (variableSlackA alpha gamma lambda * gamma * (1 - gamma) -
        ((1 - gamma) * variableSlackEta alpha gamma lambda +
          3 * variableSlackEta alpha gamma lambda)) * d := by
  have hcoef := variableSlack_marginCoefficient_lower
    halpha hgamma0 hgammaHalf hlambda
  have hd0 : (0 : ℝ) ≤ d := by positivity
  have hmul := mul_le_mul_of_nonneg_right hcoef hd0
  nlinarith

end

end WeightedEdgeColoring
