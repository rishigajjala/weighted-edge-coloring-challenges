import WeightedEdgeColoring.MultigraphColorDependentExtendedProfileBlockCapacityVarianceSelection
import WeightedEdgeColoring.MultigraphJointProfileParameters

/-!
# Scalar bounds for the colour-dependent retained-core decoder

The colour-dependent capacity rows use the unsmoothed part of the state
law.  Their leading load is therefore `rho / (1 - omega)`.  This file
records the elementary bounds for the explicit joint-profile parameters
and separates them from the graph and selection arguments.
-/

namespace WeightedEdgeColoring

noncomputable section

namespace WeightedMultigraph

/-- The rate appearing in the colour-dependent capacity rows for the
explicit joint-profile parameters. -/
def jointProfileColorDependentRate (tau : ℝ) : ℝ :=
  jointProfileRho tau / (1 - jointProfileOmega tau)

theorem jointProfile_one_sub_omega_pos
    {tau : ℝ} (htau0 : 0 < tau) (htau1 : tau ≤ 1 / 4) :
    0 < 1 - jointProfileOmega tau := by
  unfold jointProfileOmega
  linarith

theorem jointProfileColorDependentRate_eq
    {tau : ℝ} (htau0 : 0 < tau) (htau1 : tau ≤ 1 / 4) :
    jointProfileColorDependentRate tau = (1 - 2 * tau) / (1 - tau) := by
  unfold jointProfileColorDependentRate jointProfileRho jointProfileOmega
  rfl

theorem jointProfileColorDependentRate_nonneg
    {tau : ℝ} (htau0 : 0 < tau) (htau1 : tau ≤ 1 / 4) :
    0 ≤ jointProfileColorDependentRate tau := by
  rw [jointProfileColorDependentRate_eq htau0 htau1]
  exact div_nonneg (by linarith) (by linarith)

theorem jointProfileColorDependentRate_le_one
    {tau : ℝ} (htau0 : 0 < tau) (htau1 : tau ≤ 1 / 4) :
    jointProfileColorDependentRate tau ≤ 1 := by
  rw [jointProfileColorDependentRate_eq htau0 htau1]
  apply (div_le_one (by linarith)).2
  linarith

/-- The natural capacity deviation still leaves much more slot slack than
the large-edge iteration needs.  The iteration uses `tau / 8`, while the
private extra slots use `tau / 4`. -/
theorem jointProfileColorDependentRate_add_quarter_square_le
    {tau : ℝ} (htau0 : 0 < tau) (htau1 : tau ≤ 1 / 4) :
    jointProfileColorDependentRate tau + tau ^ 2 / 4 ≤ 1 - tau / 2 := by
  rw [jointProfileColorDependentRate_eq htau0 htau1]
  have hden : 0 < 1 - tau := by linarith
  have hbase :
      (1 - 2 * tau) / (1 - tau) ≤ 1 - tau / 2 - tau ^ 2 / 4 := by
    apply (div_le_iff₀ hden).2
    nlinarith [sq_nonneg tau,
      mul_nonneg htau0.le (sub_nonneg.mpr (by linarith : tau ≤ 1))]
  calc
    (1 - 2 * tau) / (1 - tau) + tau ^ 2 / 4 ≤
        (1 - tau / 2 - tau ^ 2 / 4) + tau ^ 2 / 4 := by
      linarith
    _ = 1 - tau / 2 := by ring

theorem retainedIterationGamma_pos
    {tau : ℝ} (htau : 0 < tau) : 0 < tau / 8 := by positivity

theorem retainedIterationGamma_le_half
    {tau : ℝ} (htau : tau ≤ 1 / 4) : tau / 8 ≤ 1 / 2 := by
  linarith

theorem retainedExtraGamma_eq_twice_iteration (tau : ℝ) :
    tau / 4 = 2 * (tau / 8) := by ring

theorem retainedExtraGamma_le_half
    {tau : ℝ} (htau0 : 0 ≤ tau) (htau1 : tau ≤ 1 / 4) :
    tau / 4 ≤ 1 / 2 := by linarith

/-- If `tau ≤ C0/32`, the natural colour-dependent capacity normalization
is already at least one.  Hence its common mean is admissible with the
natural selector mean bound `n`. -/
theorem jointProfile_colorDependentCapacityMean_le
    {tau C0 : ℝ} {n : ℕ}
    (htau0 : 0 < tau) (htau1 : tau ≤ 1 / 4)
    (hC0 : 0 < C0) (htauC0 : tau ≤ C0 / 32) (hn : 0 < n) :
    (n : ℝ) *
          (jointProfileRho tau / (1 - jointProfileOmega tau)) /
        colorDependentCandidateCapacityScale
          (jointProfileRho tau) (jointProfileS tau)
          (jointProfileOmega tau) (jointProfileBeta tau)
          (jointProfileQ tau) (jointProfileR tau) C0 ≤ n := by
  let M : ℝ := extendedProfileStateBound
    (jointProfileBeta tau) (jointProfileQ tau) (jointProfileR tau)
  let scale := colorDependentCandidateCapacityScale
    (jointProfileRho tau) (jointProfileS tau)
    (jointProfileOmega tau) (jointProfileBeta tau)
    (jointProfileQ tau) (jointProfileR tau) C0
  have hMnat : 1 ≤ extendedProfileStateBound
      (jointProfileBeta tau) (jointProfileQ tau) (jointProfileR tau) := by
    unfold extendedProfileStateBound
    omega
  have hM : (1 : ℝ) ≤ M := by
    dsimp [M]
    exact_mod_cast hMnat
  have hrhoHalf : (1 / 2 : ℝ) ≤ jointProfileRho tau := by
    unfold jointProfileRho
    linarith
  have hsHalf : (1 / 2 : ℝ) ≤ jointProfileS tau := by
    unfold jointProfileS
    linarith
  have hM2 : (1 : ℝ) ≤ M ^ 2 := by nlinarith [sq_nonneg (M - 1)]
  have hC0Tau : 32 * tau ≤ C0 := by nlinarith
  have hnum : tau ^ 2 ≤
      jointProfileRho tau * jointProfileS tau * C0 * M ^ 2 := by
    calc
      tau ^ 2 ≤ 8 * tau := by nlinarith
      _ = (1 / 2 : ℝ) * (1 / 2) * (32 * tau) * 1 := by ring
      _ ≤ jointProfileRho tau * jointProfileS tau * C0 * M ^ 2 := by
        gcongr
  have hscaleOne : 1 ≤ scale := by
    change 1 ≤ jointProfileRho tau * jointProfileS tau * C0 * (M / tau) ^ 2
    calc
      (1 : ℝ) = tau ^ 2 / tau ^ 2 := by
        field_simp [htau0.ne']
      _ ≤ (jointProfileRho tau * jointProfileS tau * C0 * M ^ 2) /
          tau ^ 2 := div_le_div_of_nonneg_right hnum (sq_nonneg tau)
      _ = jointProfileRho tau * jointProfileS tau * C0 * (M / tau) ^ 2 := by
        field_simp [htau0.ne']
  have hscale0 : 0 < scale := lt_of_lt_of_le zero_lt_one hscaleOne
  have hrate : jointProfileRho tau / (1 - jointProfileOmega tau) ≤ 1 :=
    jointProfileColorDependentRate_le_one htau0 htau1
  have hrateScale :
      jointProfileRho tau / (1 - jointProfileOmega tau) ≤ scale :=
    hrate.trans hscaleOne
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  change (n : ℝ) *
      (jointProfileRho tau / (1 - jointProfileOmega tau)) / scale ≤ n
  apply (div_le_iff₀ hscale0).2
  exact mul_le_mul_of_nonneg_left hrateScale hnR.le

/-- The exact unused fraction in a tiny reservoir. -/
theorem jointProfile_one_sub_colorDependentRate_mul_r_eq
    {tau : ℝ} (htau0 : 0 < tau) (htau1 : tau ≤ 1 / 4) :
    (1 - jointProfileColorDependentRate tau) * jointProfileR tau =
      tau ^ 2 / (1 - tau) := by
  rw [jointProfileColorDependentRate_eq htau0 htau1]
  unfold jointProfileR
  field_simp [ne_of_gt (by linarith : 0 < 1 - tau)]
  ring

/-- A deviation of at most `tau^2/4` leaves enough room for the integral
tiny-reservoir completion, including its `2*beta` boundary error. -/
theorem jointProfile_colorDependentTinySlack
    {tau delta : ℝ}
    (htau0 : 0 < tau) (htau1 : tau ≤ 1 / 4)
    (hdelta : delta ≤ tau ^ 2 / 4) :
    delta + 2 * jointProfileBeta tau ≤
      (1 - jointProfileColorDependentRate tau) * jointProfileR tau := by
  rw [jointProfile_one_sub_colorDependentRate_mul_r_eq htau0 htau1]
  have hden : 0 < 1 - tau := by linarith
  have hsquare0 : 0 ≤ tau ^ 2 := sq_nonneg tau
  have hsquareDiv : tau ^ 2 ≤ tau ^ 2 / (1 - tau) := by
    apply (le_div_iff₀ hden).2
    nlinarith
  unfold jointProfileBeta
  nlinarith

/-- The deterministic loss in the retained target is the proposal cutoff
`gamma` plus at most `4*tau` from the two sampling factors. -/
theorem jointProfile_retainedGap_le
    {tau gamma : ℝ}
    (htau0 : 0 < tau) (htau1 : tau ≤ 1 / 4)
    (hgamma0 : 0 ≤ gamma) (hgamma1 : gamma ≤ 1) :
    1 - jointProfileRho tau * jointProfileS tau * (1 - gamma) ≤
      gamma + 4 * tau := by
  have htauLeOne : tau ≤ 1 := htau1.trans (by norm_num)
  have hquad0 : 0 ≤ 4 * tau * (1 - tau) :=
    mul_nonneg (mul_nonneg (by norm_num) htau0.le)
      (sub_nonneg.mpr htauLeOne)
  have hcoeff : 1 - gamma ≤ 1 := by linarith
  have hmul : (1 - gamma) * (4 * tau * (1 - tau)) ≤
      4 * tau * (1 - tau) :=
    by simpa using mul_le_mul_of_nonneg_right hcoeff hquad0
  have hquadLe : 4 * tau * (1 - tau) ≤ 4 * tau := by
    nlinarith
  calc
    1 - jointProfileRho tau * jointProfileS tau * (1 - gamma) =
        gamma + (1 - gamma) * (4 * tau * (1 - tau)) := by
      unfold jointProfileRho jointProfileS
      ring
    _ ≤ gamma + 4 * tau * (1 - tau) := by
      simpa [add_comm] using add_le_add_right hmul gamma
    _ ≤ gamma + 4 * tau := by
      simpa [add_comm] using add_le_add_right hquadLe gamma

/-- A reusable final decoder budget.  The selector contributes the square
error `sigma`; the large-edge nibble contributes `largeLoss`. -/
theorem jointProfile_retainedDecoderBudget_le
    {tau gamma eta epsilon ell largeLoss sigma star n : ℝ}
    (htau0 : 0 < tau) (htau1 : tau ≤ 1 / 4)
    (hgamma0 : 0 ≤ gamma) (hgamma1 : gamma ≤ 1)
    (hepsilon0 : 0 ≤ epsilon) (hell0 : 0 ≤ ell)
    (hn : 1 ≤ n) (hstar0 : 0 ≤ star) (hstar : star ≤ n)
    (hsigma0 : 0 ≤ sigma) (hsigma : sigma ≤ epsilon ^ 2 * n)
    (hlarge : largeLoss ≤ ell * n)
    (hbudget : ell + gamma + 5 * tau + epsilon ≤ eta) :
    largeLoss +
          ((1 - jointProfileRho tau * jointProfileS tau * (1 - gamma)) * star +
            Real.sqrt (star * sigma)) +
        2 * jointProfileBeta tau ≤ eta * n := by
  have hn0 : 0 ≤ n := zero_le_one.trans hn
  have hgap := jointProfile_retainedGap_le htau0 htau1 hgamma0 hgamma1
  have hgap0 : 0 ≤
      1 - jointProfileRho tau * jointProfileS tau * (1 - gamma) := by
    have hrho0 : 0 ≤ jointProfileRho tau := by
      unfold jointProfileRho
      linarith
    have hs0 : 0 ≤ jointProfileS tau := by
      unfold jointProfileS
      linarith
    have hrhos1 : jointProfileRho tau * jointProfileS tau ≤ 1 := by
      have hrho1 : jointProfileRho tau ≤ 1 := by
        unfold jointProfileRho
        linarith
      have hs1 : jointProfileS tau ≤ 1 := by
        unfold jointProfileS
        linarith
      nlinarith
    have hfactor : 0 ≤ 1 - gamma := sub_nonneg.mpr hgamma1
    have hprod := mul_le_mul_of_nonneg_right hrhos1 hfactor
    nlinarith
  have hlinear :
      (1 - jointProfileRho tau * jointProfileS tau * (1 - gamma)) * star ≤
        (gamma + 4 * tau) * n := by
    have hcoef0 : 0 ≤ gamma + 4 * tau := by positivity
    calc
      _ ≤ (gamma + 4 * tau) * star :=
        mul_le_mul_of_nonneg_right hgap hstar0
      _ ≤ (gamma + 4 * tau) * n :=
        mul_le_mul_of_nonneg_left hstar hcoef0
  have hprod0 : 0 ≤ star * sigma := mul_nonneg hstar0 hsigma0
  have hprod : star * sigma ≤ (epsilon * n) ^ 2 := by
    calc
      star * sigma ≤ n * (epsilon ^ 2 * n) :=
        mul_le_mul hstar hsigma hsigma0 hn0
      _ = (epsilon * n) ^ 2 := by ring
  have hepsilonN0 : 0 ≤ epsilon * n := mul_nonneg hepsilon0 hn0
  have hsqrt : Real.sqrt (star * sigma) ≤ epsilon * n := by
    rw [← Real.sqrt_sq hepsilonN0]
    exact Real.sqrt_le_sqrt hprod
  have hbeta : 2 * jointProfileBeta tau ≤ tau * n := by
    unfold jointProfileBeta
    have htauLeOne : tau ≤ 1 := htau1.trans (by norm_num)
    have htauSq : tau ^ 2 ≤ tau := by nlinarith
    have htauN : tau ≤ tau * n := by nlinarith
    nlinarith
  calc
    largeLoss +
          ((1 - jointProfileRho tau * jointProfileS tau * (1 - gamma)) * star +
            Real.sqrt (star * sigma)) +
        2 * jointProfileBeta tau ≤
      ell * n + ((gamma + 4 * tau) * n + epsilon * n) + tau * n := by
        gcongr
    _ = (ell + gamma + 5 * tau + epsilon) * n := by ring
    _ ≤ eta * n := mul_le_mul_of_nonneg_right hbudget hn0

/-- A canonical positive profile scale for a retained target with
`gamma < eta`.  The extra minimum keeps all profile inequalities in their
fixed small-parameter range. -/
def retainedCoreTau (C0 gamma eta : ℝ) : ℝ :=
  min ((eta - gamma) / 1024) (min (1 / 4) (C0 / 32))

theorem retainedCoreTau_pos
    {C0 gamma eta : ℝ} (hC0 : 0 < C0) (hgammaEta : gamma < eta) :
    0 < retainedCoreTau C0 gamma eta := by
  unfold retainedCoreTau
  exact lt_min (div_pos (sub_pos.mpr hgammaEta) (by norm_num))
    (lt_min (by norm_num) (div_pos hC0 (by norm_num)))

theorem retainedCoreTau_le_quarter (C0 gamma eta : ℝ) :
    retainedCoreTau C0 gamma eta ≤ 1 / 4 := by
  exact (min_le_right _ _).trans (min_le_left _ _)

theorem retainedCoreTau_le_C0_div
    (C0 gamma eta : ℝ) :
    retainedCoreTau C0 gamma eta ≤ C0 / 32 := by
  exact (min_le_right _ _).trans (min_le_right _ _)

theorem retainedCoreTau_le_gap
    {C0 gamma eta : ℝ} :
    1024 * retainedCoreTau C0 gamma eta ≤ eta - gamma := by
  unfold retainedCoreTau
  have h := min_le_left ((eta - gamma) / 1024)
    (min (1 / 4) (C0 / 32))
  linarith

/-- The canonical scale leaves a fixed fraction of the available
`eta-gamma` gap for the large-edge loss and the quadratic error. -/
theorem retainedCoreTau_final_budget
    {C0 gamma eta : ℝ} (hgammaEta : gamma < eta) :
    (eta - gamma) / 4 + gamma +
        5 * retainedCoreTau C0 gamma eta +
          (eta - gamma) / 1024 ≤ eta := by
  have htau := retainedCoreTau_le_gap (C0 := C0) (gamma := gamma) (eta := eta)
  linarith

/-- The repeated retained-residual charge in the large-edge capture costs
at most one quarter of the available gap.  The factor eight is the worst
coefficient produced when the extra-slot parameter is at most one half. -/
theorem retainedCoreTau_largeCapture_with_trace_le
    {C0 gamma eta trace : ℝ}
    (hgamma0 : 0 ≤ gamma) (hgammaEta : 64 * gamma < eta)
    (htrace : trace ≤ (eta - gamma) / 64) :
    trace + 8 * (gamma + 4 * retainedCoreTau C0 gamma eta +
        (eta - gamma) / 1024) ≤ (eta - gamma) / 4 := by
  have hgap0 : 0 < eta - gamma := by nlinarith
  have hgammaGap : 63 * gamma < eta - gamma := by nlinarith
  have htau := retainedCoreTau_le_gap
    (C0 := C0) (gamma := gamma) (eta := eta)
  nlinarith

theorem retainedCoreTau_tinySlack
    {C0 gamma eta delta : ℝ}
    (hC0 : 0 < C0) (hgammaEta : gamma < eta)
    (hdelta : delta ≤ retainedCoreTau C0 gamma eta ^ 2 / 4) :
    delta + 2 * jointProfileBeta (retainedCoreTau C0 gamma eta) ≤
      (1 - jointProfileColorDependentRate
        (retainedCoreTau C0 gamma eta)) *
          jointProfileR (retainedCoreTau C0 gamma eta) := by
  exact jointProfile_colorDependentTinySlack
    (retainedCoreTau_pos hC0 hgammaEta)
    (retainedCoreTau_le_quarter C0 gamma eta) hdelta

/-- Final retained-core budget with the canonical split: one quarter of
the available gap pays the large matching loss and one quarter pays the
square-root selector error. -/
theorem retainedCoreTau_decoderBudget_le
    {C0 gamma eta largeLoss sigma star n : ℝ}
    (hC0 : 0 < C0) (hgamma0 : 0 ≤ gamma) (hgamma1 : gamma ≤ 1)
    (hgammaEta : gamma < eta)
    (hn : 1 ≤ n) (hstar0 : 0 ≤ star) (hstar : star ≤ n)
    (hsigma0 : 0 ≤ sigma)
    (hsigma : sigma ≤ ((eta - gamma) / 1024) ^ 2 * n)
    (hlarge : largeLoss ≤ (eta - gamma) / 4 * n) :
    largeLoss +
          ((1 - jointProfileRho (retainedCoreTau C0 gamma eta) *
              jointProfileS (retainedCoreTau C0 gamma eta) * (1 - gamma)) *
              star + Real.sqrt (star * sigma)) +
        2 * jointProfileBeta (retainedCoreTau C0 gamma eta) ≤ eta * n := by
  apply jointProfile_retainedDecoderBudget_le
    (retainedCoreTau_pos hC0 hgammaEta)
    (retainedCoreTau_le_quarter C0 gamma eta)
    hgamma0 hgamma1
    (div_nonneg (sub_nonneg.mpr hgammaEta.le) (by norm_num))
    (div_nonneg (sub_nonneg.mpr hgammaEta.le) (by norm_num))
    hn hstar0 hstar hsigma0 hsigma hlarge
  exact retainedCoreTau_final_budget hgammaEta

end WeightedMultigraph

end

end WeightedEdgeColoring
