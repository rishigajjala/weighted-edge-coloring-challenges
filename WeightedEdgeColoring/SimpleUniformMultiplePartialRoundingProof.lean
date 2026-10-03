import WeightedEdgeColoring.PaddedSimpleRoundingReduction
import WeightedEdgeColoring.UniformConcreteProfileBalancing
import WeightedEdgeColoring.ExtendedProfileBlockJointFeasibility
import WeightedEdgeColoring.ExtendedProfileJointOuterBounds
import WeightedEdgeColoring.ExtendedProfileSelectedClosedPartialRounding
import WeightedEdgeColoring.DyadicSimpleOuterStructuralScales
import WeightedEdgeColoring.VariableSlackGeometricSteps
import WeightedEdgeColoring.VariableSlackIterationScalars
import WeightedEdgeColoring.LargeEdgeExtraCaptureDyadic

/-!
# Uniform partial rounding for weighted simple graphs

This file fixes all parameters in the selected-profile, dyadic,
raw-sample-then-isolate construction.  The only threshold in the final
statement is the palette size.
-/

open scoped BigOperators

namespace WeightedEdgeColoring

noncomputable section

open WeightedSimpleGraph
open RankThreeOptionSystem.OriginalIterationState

universe u

private def simpleNibbleAlpha : ℝ := 1 / 200000

private theorem simpleNibbleAlpha_pos : 0 < simpleNibbleAlpha := by
  norm_num [simpleNibbleAlpha]

/- The selected-profile isolated iteration gives the exact-multiple
partial-rounding statement used by the padding reduction. -/
set_option maxHeartbeats 800000 in
theorem simpleUniformMultiplePartialRounding_proved :
    SimpleUniformMultiplePartialRounding.{u} := by
  intro eta heta
  let eps : ℝ := min (eta / 37) (1 / 2)
  have heps0 : 0 < eps := lt_min (div_pos heta (by norm_num)) (by norm_num)
  have heps1 : eps ≤ 1 := (min_le_right _ _).trans (by norm_num)
  have h37eps : 37 * eps ≤ eta := by
    have := min_le_left (eta / 37) (1 / 2)
    nlinarith
  let tau : ℝ := eps / 8
  let gamma : ℝ := tau / 8
  let extraGamma : ℝ := tau / 4
  let alpha : ℝ := simpleNibbleAlpha
  let delta : ℝ := 1 / 2
  have htau0 : 0 < tau := by dsimp [tau]; positivity
  have htauQuarter : tau ≤ 1 / 4 := by
    dsimp [tau]
    linarith
  have hgamma0 : 0 < gamma := by dsimp [gamma]; positivity
  have hgammaHalf : gamma ≤ 1 / 2 := by
    dsimp [gamma, tau]
    linarith
  have hextraGamma0 : 0 ≤ extraGamma := by dsimp [extraGamma]; positivity
  have hextraGammaHalf : extraGamma ≤ 1 / 2 := by
    dsimp [extraGamma, tau]
    linarith
  have hextraEq : extraGamma = 2 * gamma := by
    dsimp [extraGamma, gamma]
    ring
  have halpha : 0 < alpha := by simpa [alpha] using simpleNibbleAlpha_pos
  have halphaSmall : alpha ≤ 1 / 100000 := by
    norm_num [alpha, simpleNibbleAlpha]
  have halphaSixth : alpha ≤ 1 / 6 := by
    norm_num [alpha, simpleNibbleAlpha]
  have hdelta0 : 0 < delta := by norm_num [delta]
  have hdelta1 : delta ≤ 1 := by norm_num [delta]
  rcases jointProfile_parameters htau0 htauQuarter with
    ⟨hspos, hbeta, hqpos, hrpos, homega0, homega1, hleft, hr1,
      hrhopos, hrhoKappa, hfraction⟩
  let s := jointProfileS tau
  let beta := jointProfileBeta tau
  let q := jointProfileQ tau
  let r := jointProfileR tau
  let omega := jointProfileOmega tau
  let rho := jointProfileRho tau
  have hs : 0 ≤ s := by simpa [s] using hspos.le
  have hs1 : s ≤ 1 := by dsimp [s, jointProfileS]; linarith
  have hq : 0 ≤ q := by simpa [q] using hqpos.le
  have hr0 : 0 ≤ r := by simpa [r] using hrpos.le
  have hbeta0 : 0 < beta := by simpa [beta] using hbeta
  have hbeta1 : beta ≤ 1 := by
    dsimp [beta, jointProfileBeta]
    nlinarith [sq_nonneg tau]
  have hrho : 0 < rho := by simpa [rho] using hrhopos
  have hrs : rho * s ≤ 1 := by
    dsimp [rho, s, jointProfileRho, jointProfileS]
    nlinarith [sq_nonneg (1 - 2 * tau)]
  have hrhoLoss : 1 - rho * s ≤ eps := by
    dsimp [rho, s, jointProfileRho, jointProfileS, tau]
    nlinarith [sq_nonneg eps]
  obtain ⟨k, Nquad, hk, hquad⟩ :=
    WeightedSimpleGraph.exists_jointProfile_blockWidth_quadraticBound_le
      htau0 htauQuarter heps0
  obtain ⟨Njoint, hjoint⟩ :=
    jointProfile_scalarSlack_eventually hk htau0 htauQuarter
  obtain ⟨Nordinary, hordinary⟩ :=
    WeightedSimpleGraph.jointProfile_ordinaryRate_eventually
      hk htau0 htauQuarter
  obtain ⟨L, hdyadicCover, hdyadicTopLt⟩ :=
    exists_dyadic_scale_mem_Ico_one_two beta hbeta0 hbeta1
  have hdyadicTop : dyadicScale beta L ≤ 2 := hdyadicTopLt.le
  let placeCount := explicitLargeSlotBound beta q r
  let scale := extendedProfileCandidateCapacityScale rho s omega beta q r
  let A := dyadicSimpleCodegreeCoefficient placeCount scale
  let Ecoef := dyadicSimpleSupportCoefficient beta extraGamma
  let Ccoef := dyadicSimpleChoiceCoefficient placeCount beta extraGamma
  have hA : 0 < A := by dsimp [A, dyadicSimpleCodegreeCoefficient]; omega
  have hCcoef : 0 < Ccoef := by
    dsimp [Ccoef, dyadicSimpleChoiceCoefficient, Ecoef,
      dyadicSimpleSupportCoefficient]
    omega
  let traceEps : ℝ := eps / 2
  have htraceEps0 : 0 < traceEps := by dsimp [traceEps]; positivity
  have htraceEps1 : traceEps ≤ 1 := by dsimp [traceEps]; linarith
  let T := variableSlackStepMultiplier alpha gamma traceEps
  let decayBudget : ℝ := 3 * alpha * gamma * T
  let cfrac : ℝ := Real.exp (-2 * decayBudget) / 4
  have hcfrac : 0 < cfrac := by dsimp [cfrac]; positivity
  have hscale0 : 0 < scale := by
    exact extendedProfileCandidateCapacityScale_pos hrho hspos homega0
  have hgapExtra : extraGamma < 1 :=
    hextraGammaHalf.trans_lt (by norm_num)
  have hclosedEventually := eventually_dyadicSimple_closedRoundScales
    A 1 alpha gamma delta cfrac hA (by norm_num) halpha hgamma0 hdelta0 hcfrac
  have hboundaryEventually :=
    eventually_dyadicSimple_fixedEndpointBlock_sublinear
      (L + 1) traceEps htraceEps0
  have hlossEventually := eventually_const_le_pos_mul_nat
    ((Ccoef : ℝ) + 1) gamma hgamma0
  have hpairEventually := eventually_const_le_pos_mul_nat scale 1 (by norm_num)
  have hmarginEventually := eventually_const_le_pos_mul_nat
    (4 * (1 - gamma) * A) (alpha * gamma ^ 2 * cfrac) (by positivity)
  have hfloorEventually := eventually_const_le_pos_mul_nat
    (T * A) (Real.exp (-2 * decayBudget) / 4) (by positivity)
  have hdecoderEventually := eventually_const_le_pos_mul_nat 1 eps heps0
  have hrootEventually : ∀ᶠ m : ℕ in Filter.atTop, 1 ≤ m :=
    Filter.eventually_ge_atTop 1
  have hall : ∀ᶠ m : ℕ in Filter.atTop,
      (∀ d lambda : ℕ, 0 < d → 0 < lambda →
        cfrac * dyadicSimpleQuantizationScale m ≤ d →
        d ≤ (m + 1) ^ 30 →
        lambda ≤ dyadicSimpleCodegreeScale A m →
        DyadicSimpleClosedRoundScales 1 m d lambda alpha gamma delta) ∧
      (dyadicSimpleEndpointBlockScale (L + 1) m : ℝ) ≤
        traceEps * dyadicSimplePaletteScale m ∧
      (Ccoef : ℝ) + 1 ≤ gamma * m ∧
      scale ≤ (m : ℝ) ∧
      4 * (1 - gamma) * A ≤ alpha * gamma ^ 2 * cfrac * m ∧
      T * A ≤ Real.exp (-2 * decayBudget) / 4 * m ∧
      1 ≤ eps * m ∧ 1 ≤ m := by
    filter_upwards [hclosedEventually, hboundaryEventually, hlossEventually,
      hpairEventually, hmarginEventually, hfloorEventually,
      hdecoderEventually, hrootEventually] with m hclosed hboundary hloss
        hpair hmargin hfloor hdecoder hm
    exact ⟨hclosed, hboundary, hloss, by simpa using hpair, hmargin, hfloor,
      hdecoder, hm⟩
  rcases Filter.eventually_atTop.1 hall with ⟨M, hM⟩
  have hMone : 1 ≤ M := (hM M le_rfl).2.2.2.2.2.2.2
  refine ⟨max (max Nquad Njoint) (max Nordinary (M ^ 20)), k, hk, ?_⟩
  intro G B hpaletteLarge hpack
  let palette := B * k
  have hquadPalette : Nquad ≤ palette :=
    (le_max_left Nquad Njoint).trans
      ((le_max_left (max Nquad Njoint) (max Nordinary (M ^ 20))).trans
        hpaletteLarge)
  have hjointPalette : Njoint ≤ palette :=
    (le_max_right Nquad Njoint).trans
      ((le_max_left (max Nquad Njoint) (max Nordinary (M ^ 20))).trans
        hpaletteLarge)
  have hordPalette : Nordinary ≤ palette :=
    (le_max_left Nordinary (M ^ 20)).trans
      ((le_max_right (max Nquad Njoint) (max Nordinary (M ^ 20))).trans
        hpaletteLarge)
  have hMpow : M ^ 20 ≤ palette :=
    (le_max_right Nordinary (M ^ 20)).trans
      ((le_max_right (max Nquad Njoint) (max Nordinary (M ^ 20))).trans
        hpaletteLarge)
  have hn : 0 < palette := by
    have hMpos : 0 < M := Nat.zero_lt_one.trans_le hMone
    exact lt_of_lt_of_le (pow_pos hMpos 20) hMpow
  have hB : 0 < B := by
    by_contra hB0
    have : B = 0 := Nat.eq_zero_of_not_pos hB0
    simp [palette, this] at hn
  let m := dyadicSimpleRoot palette
  have hmM : M ≤ m := le_dyadicSimpleRoot_of_pow_le hMpow
  rcases hM m hmM with
    ⟨hclosed, hboundary, hloss, hpair, hmarginGrowth, hfloorGrowth,
      hdecoderGrowth, hm⟩
  have hpaletteLower : m ^ 20 ≤ palette := dyadicSimpleRoot_pow_le palette
  have hpaletteUpper : palette ≤ 2 ^ 20 * m ^ 20 :=
    dyadicSimple_palette_le_two_pow_mul hm
      (lt_succ_dyadicSimpleRoot_pow palette)
  let N := dyadicSimpleQuantizationScale m
  let reserve := dyadicSimpleReserveScale m
  let lambda := dyadicSimpleCodegreeScale A m
  let E := Ecoef * m ^ 20
  let C := Ccoef * m ^ 20
  let d0 := N - C
  let S0 := fixedSlackPaddedSlotTarget gamma d0
  let K := dyadicSimpleEndpointBlockScale 1 m
  let steps := variableSlackSteps alpha gamma traceEps lambda
  have hN : 0 < N := by
    dsimp [N]
    exact (dyadicSimple_scales_pos m (by omega)).2.1
  have hreserve : 0 < reserve := by
    dsimp [reserve]
    exact (dyadicSimple_scales_pos m (by omega)).2.2
  have hlambda : 0 < lambda := by
    dsimp [lambda, dyadicSimpleCodegreeScale]
    exact Nat.mul_pos hA (pow_pos (by omega) _)
  have hK : 0 < K := by
    dsimp [K, dyadicSimpleEndpointBlockScale]
    positivity
  have hlossReal : (C : ℝ) + 1 ≤ gamma * N := by
    have hmR : (1 : ℝ) ≤ m := by exact_mod_cast hm
    have hm20 : (1 : ℝ) ≤ (m : ℝ) ^ 20 := one_le_pow₀ hmR
    have hm_to_m10 : (m : ℝ) ≤ (m : ℝ) ^ 10 := by
      calc
        (m : ℝ) = (m : ℝ) ^ 1 := by ring
        _ ≤ (m : ℝ) ^ 10 := pow_le_pow_right₀ hmR (by omega)
    have hgrowth : (Ccoef : ℝ) + 1 ≤ gamma * (m : ℝ) ^ 10 :=
      hloss.trans (mul_le_mul_of_nonneg_left hm_to_m10 hgamma0.le)
    dsimp [C, N, dyadicSimpleQuantizationScale]
    push_cast
    calc
      (Ccoef : ℝ) * (m : ℝ) ^ 20 + 1 ≤
          (Ccoef : ℝ) * (m : ℝ) ^ 20 + 1 * (m : ℝ) ^ 20 :=
        by
          simpa [add_comm] using
            (add_le_add_left hm20 ((Ccoef : ℝ) * (m : ℝ) ^ 20))
      _ = ((Ccoef : ℝ) + 1) * (m : ℝ) ^ 20 := by ring
      _ ≤ (gamma * (m : ℝ) ^ 10) * (m : ℝ) ^ 20 :=
        mul_le_mul_of_nonneg_right hgrowth (by positivity)
      _ = gamma * (m : ℝ) ^ 30 := by ring
  have hCN : C ≤ N := by
    have hgamma1 : gamma ≤ 1 := hgammaHalf.trans (by norm_num)
    have hreal : (C : ℝ) ≤ N := by
      nlinarith [mul_le_mul_of_nonneg_right hgamma1
        (show (0 : ℝ) ≤ N by positivity)]
    exact_mod_cast hreal
  have hNC : 0 < N - C := by
    have hstrict : (C : ℝ) < N := by
      have hgammaStrict : gamma < 1 := hgammaHalf.trans_lt (by norm_num)
      have hN0 : (0 : ℝ) < N := by exact_mod_cast hN
      nlinarith
    exact Nat.sub_pos_of_lt (by exact_mod_cast hstrict)
  have hslotCaps := dyadicSimple_initial_slot_caps hgamma0.le hgammaHalf
    hCN hlossReal (show 1 - tau / 2 ≤ 1 - 4 * gamma by
      dsimp [gamma]; ring_nf; exact le_rfl)
  have hordinarySlotCap : (N : ℝ) * (1 - tau / 2) ≤ S0 := by
    simpa [S0, d0] using hslotCaps.1
  have hextraSlotCap : (1 - extraGamma) * N ≤ S0 := by
    rw [hextraEq]
    simpa [S0, d0] using hslotCaps.2.1
  have hgap0 : (S0 : ℝ) ≤ (1 - gamma) * d0 := by
    dsimp [S0, d0]
    rw [Nat.cast_sub hCN]
    exact hslotCaps.2.2
  have hsupportE :
      2 * (((palette : ℝ) / beta / (1 - extraGamma)) + 1 + reserve) ≤ E := by
    simpa [E, reserve, Ecoef] using
      (dyadicSimple_support_budget hm hbeta0 hgapExtra hpaletteUpper)
  have hchoiceCap : palette * placeCount * placeCount + E ≤ C := by
    simpa [E, C, Ecoef, Ccoef] using
      (dyadicSimple_choice_budget
        (m := m) (palette := palette) (placeCount := placeCount)
        (beta := beta) (extraGamma := extraGamma) hpaletteUpper)
  have hordinaryJobCodegree : (N : ℝ) *
      ((placeCount : ℝ) * scale / palette) ≤ lambda := by
    simpa [N, lambda, A] using dyadicSimple_ordinaryJobCodegree
      hm hscale0.le hpaletteLower
  have hextraCodegree : (N : ℝ) / reserve ≤ lambda := by
    simpa [N, reserve, lambda] using
      dyadicSimple_extraCodegree_for_coefficient hm (show 1 ≤ A by omega)
  have hordinaryPair : scale / (palette : ℝ) ≤ 1 / (reserve : ℝ) := by
    have hpaletteR : (0 : ℝ) < palette := by exact_mod_cast hn
    have hreserveR : (0 : ℝ) < reserve := by exact_mod_cast hreserve
    rw [div_le_div_iff₀ hpaletteR hreserveR]
    simp only [one_mul]
    have hmR : (1 : ℝ) ≤ m := by exact_mod_cast hm
    have hm4 : (m : ℝ) ≤ m ^ 4 := by
      calc
        (m : ℝ) = (m : ℝ) ^ 1 := by ring
        _ ≤ (m : ℝ) ^ 4 := pow_le_pow_right₀ hmR (by omega)
    have hscale4 : scale ≤ (m : ℝ) ^ 4 := hpair.trans hm4
    have hresCast : (reserve : ℝ) = (m : ℝ) ^ 16 := by
      simp [reserve, dyadicSimpleReserveScale]
    have hpalCast : (m : ℝ) ^ 20 ≤ palette := by exact_mod_cast hpaletteLower
    rw [hresCast]
    calc
      scale * (m : ℝ) ^ 16 ≤ (m : ℝ) ^ 4 * (m : ℝ) ^ 16 := by gcongr
      _ = (m : ℝ) ^ 20 := by ring
      _ ≤ palette := hpalCast
  have hret0 : 0 ≤ fixedSlackJobRetention
      (variableSlackA alpha gamma lambda) gamma -
        variableSlackEta alpha gamma lambda :=
    (variableSlack_jobRetention_pos halpha hgamma0 hgammaHalf hlambda
      (by linarith : alpha ≤ 1)).le
  have hretHalf : 1 / 2 ≤ fixedSlackJobRetention
      (variableSlackA alpha gamma lambda) gamma -
        variableSlackEta alpha gamma lambda :=
    variableSlack_half_le_jobRetention halpha.le halphaSixth hgamma0.le
      (hgammaHalf.trans (by norm_num)) hlambda
  have hret1 : fixedSlackJobRetention
      (variableSlackA alpha gamma lambda) gamma -
        variableSlackEta alpha gamma lambda ≤ 1 :=
    variableSlack_jobRetention_le_one halpha.le hgamma0.le
      (hgammaHalf.trans (by norm_num)) hlambda
  have hstepsCast : (steps : ℝ) ≤ T * lambda := by
    simpa [steps, T] using variableSlackSteps_cast_le halpha hgamma0
      htraceEps0 htraceEps1 hlambda
  have hdecay :
      (1 - (fixedSlackJobRetention (variableSlackA alpha gamma lambda) gamma -
        variableSlackEta alpha gamma lambda)) * steps ≤ decayBudget := by
    simpa [decayBudget, T] using variableSlack_jobDecay_mul_steps_le
      halpha.le hgamma0.le (hgammaHalf.trans (by norm_num)) hlambda hstepsCast
  have hfloorSteps : (steps : ℝ) ≤
      Real.exp (-2 * decayBudget) * (1 / 2 : ℝ) * N / 2 := by
    have hmR : (1 : ℝ) ≤ m := by exact_mod_cast hm
    have hm15 : (m : ℝ) ^ 15 ≤ (m : ℝ) ^ 30 :=
      pow_le_pow_right₀ hmR (by omega)
    have hstep0 : (0 : ℝ) ≤ T := by
      dsimp [T, variableSlackStepMultiplier]
      have hinv : 1 ≤ 1 / traceEps :=
        (le_div_iff₀ htraceEps0).2 (by simpa using htraceEps1)
      have : 0 ≤ Real.log (1 / traceEps) := Real.log_nonneg hinv
      positivity
    have hlambdaCast : (lambda : ℝ) = (A : ℝ) * (m : ℝ) ^ 14 := by
      simp [lambda, dyadicSimpleCodegreeScale]
    have hm16 : (m : ℝ) ≤ (m : ℝ) ^ 16 := by
      calc
        (m : ℝ) = (m : ℝ) ^ 1 := by ring
        _ ≤ (m : ℝ) ^ 16 := pow_le_pow_right₀ hmR (by omega)
    have hTA : T * A ≤ Real.exp (-2 * decayBudget) / 4 * (m : ℝ) ^ 16 :=
      hfloorGrowth.trans
        (mul_le_mul_of_nonneg_left hm16 (by positivity))
    calc
      (steps : ℝ) ≤ T * lambda := hstepsCast
      _ = (T * A) * (m : ℝ) ^ 14 := by rw [hlambdaCast]; ring
      _ ≤ (Real.exp (-2 * decayBudget) / 4 * (m : ℝ) ^ 16) *
          (m : ℝ) ^ 14 := by gcongr
      _ = Real.exp (-2 * decayBudget) * (1 / 2 : ℝ) * N / 2 := by
        simp [N, dyadicSimpleQuantizationScale]
        ring
  have hd0Half : (1 / 2 : ℝ) * N ≤ d0 := by
    dsimp [d0]
    rw [Nat.cast_sub hCN]
    have hCgamma : (C : ℝ) ≤ gamma * N := by
      linarith only [hlossReal]
    have hgammaN : gamma * (N : ℝ) ≤ (1 / 2 : ℝ) * N :=
      mul_le_mul_of_nonneg_right hgammaHalf (Nat.cast_nonneg N)
    linarith only [hCgamma, hgammaN]
  have hdegreeFraction : ∀ n ≤ steps,
      cfrac * N ≤
        RankThreeOptionSystem.OriginalIterationState.naturalSharpJobScale
          d0 (variableSlackA alpha gamma lambda) gamma
          (variableSlackEta alpha gamma lambda) n := by
    have hfrac := naturalSharpJobScale_uniform_fraction d0 N steps
      (variableSlackA alpha gamma lambda) gamma
      (variableSlackEta alpha gamma lambda) (1 / 2) decayBudget
      hret0 hretHalf hret1 (by norm_num) hd0Half hdecay hfloorSteps
    intro n hnstep
    have h := hfrac n hnstep
    dsimp [cfrac]
    convert h using 1 <;> ring
  have hdegreeUpper : ∀ n,
      RankThreeOptionSystem.OriginalIterationState.naturalSharpJobScale
          d0 (variableSlackA alpha gamma lambda) gamma
          (variableSlackEta alpha gamma lambda) n ≤ (m + 1) ^ 30 := by
    intro n
    exact (naturalSharpJobScale_le_initial d0 n
        (variableSlackA alpha gamma lambda) gamma
        (variableSlackEta alpha gamma lambda) hret0 hret1).trans
      ((Nat.sub_le N C).trans (Nat.pow_le_pow_left (Nat.le_succ m) 30))
  have hroundScales : ∀ n < steps,
      DyadicSimpleClosedRoundScales 1 m
        (RankThreeOptionSystem.OriginalIterationState.naturalSharpJobScale
          d0 (variableSlackA alpha gamma lambda) gamma
          (variableSlackEta alpha gamma lambda) n)
        lambda alpha gamma delta := by
    intro n hnstep
    apply hclosed
    · have := hdegreeFraction n (Nat.le_of_lt hnstep)
      have hNpos : (0 : ℝ) < N := by exact_mod_cast hN
      exact_mod_cast (mul_pos hcfrac hNpos).trans_le this
    · exact hlambda
    · exact hdegreeFraction n (Nat.le_of_lt hnstep)
    · exact hdegreeUpper n
    · exact le_rfl
  have hmarginDegree : ∀ n < steps,
      4 * (1 - gamma) ≤ variableSlackA alpha gamma lambda * gamma *
        RankThreeOptionSystem.OriginalIterationState.naturalSharpJobScale
          d0 (variableSlackA alpha gamma lambda) gamma
          (variableSlackEta alpha gamma lambda) n := by
    intro n hnstep
    let d := RankThreeOptionSystem.OriginalIterationState.naturalSharpJobScale
      d0 (variableSlackA alpha gamma lambda) gamma
      (variableSlackEta alpha gamma lambda) n
    have hd := hdegreeFraction n (Nat.le_of_lt hnstep)
    have hlambdaCast : (lambda : ℝ) = (A : ℝ) * (m : ℝ) ^ 14 := by
      simp [lambda, dyadicSimpleCodegreeScale]
    have hmR : (1 : ℝ) ≤ m := by exact_mod_cast hm
    have hm15 : (m : ℝ) ^ 15 ≤ (m : ℝ) ^ 30 :=
      pow_le_pow_right₀ hmR (by omega)
    have hgrowth : 4 * (1 - gamma) * (lambda : ℝ) ≤
        alpha * gamma ^ 2 * (cfrac * N) := by
      rw [hlambdaCast]
      calc
        4 * (1 - gamma) * ((A : ℝ) * (m : ℝ) ^ 14) =
            (4 * (1 - gamma) * A) * (m : ℝ) ^ 14 := by ring
        _ ≤ (alpha * gamma ^ 2 * cfrac * m) * (m : ℝ) ^ 14 :=
          mul_le_mul_of_nonneg_right hmarginGrowth (by positivity)
        _ = alpha * gamma ^ 2 * cfrac * (m : ℝ) ^ 15 := by ring
        _ ≤ alpha * gamma ^ 2 * cfrac * (m : ℝ) ^ 30 :=
          mul_le_mul_of_nonneg_left hm15 (by positivity)
        _ = alpha * gamma ^ 2 * (cfrac * N) := by
          simp [N, dyadicSimpleQuantizationScale]
          ring
    have hright := mul_le_mul_of_nonneg_left hd
      (show 0 ≤ alpha * gamma ^ 2 by positivity)
    change 4 * (1 - gamma) ≤
      variableSlackA alpha gamma lambda * gamma * (d : ℝ)
    unfold variableSlackA
    rw [show (alpha * gamma / (lambda : ℝ)) * gamma * (d : ℝ) =
      (alpha * gamma ^ 2 * d) / lambda by ring]
    exact (le_div_iff₀ (by positivity : (0 : ℝ) < lambda)).2
      (hgrowth.trans hright)
  have hmargin : ∀ n < steps, 1 - gamma ≤
      (variableSlackA alpha gamma lambda * gamma * (1 - gamma) -
        ((1 - gamma) * variableSlackEta alpha gamma lambda +
          3 * variableSlackEta alpha gamma lambda)) *
        RankThreeOptionSystem.OriginalIterationState.naturalSharpJobScale
          d0 (variableSlackA alpha gamma lambda) gamma
          (variableSlackEta alpha gamma lambda) n := by
    intro n hnstep
    exact variableSlack_iterationMargin_of_degree halpha.le hgamma0.le
      hgammaHalf hlambda (hmarginDegree n hnstep)
  have hnextPositive : ∀ n < steps,
      0 < (fixedSlackJobRetention (variableSlackA alpha gamma lambda) gamma -
          variableSlackEta alpha gamma lambda) *
        RankThreeOptionSystem.OriginalIterationState.naturalSharpJobScale
          d0 (variableSlackA alpha gamma lambda) gamma
          (variableSlackEta alpha gamma lambda) n := by
    intro n hnstep
    exact mul_pos (lt_of_lt_of_le (by norm_num) hretHalf)
      (by exact_mod_cast (hroundScales n hnstep).degree_five.trans' (by omega))
  have htheta1 :
      (1 - delta) * variableSlackA alpha gamma lambda / 8 ≤ 1 := by
    have haLe : variableSlackA alpha gamma lambda ≤ alpha := by
      unfold variableSlackA
      have hlambdaOne : (1 : ℝ) ≤ lambda := by exact_mod_cast hlambda
      apply (div_le_iff₀ (by positivity : (0 : ℝ) < lambda)).2
      exact (mul_le_mul_of_nonneg_left
        (hgammaHalf.trans (by norm_num : (1 / 2 : ℝ) ≤ 1)) halpha.le).trans
          (mul_le_mul_of_nonneg_left hlambdaOne halpha.le)
    norm_num [delta, alpha, simpleNibbleAlpha] at haLe ⊢
    linarith only [haLe]
  have haSmall : variableSlackA alpha gamma lambda ≤ delta / 96 := by
    have haLe : variableSlackA alpha gamma lambda ≤ alpha := by
      unfold variableSlackA
      apply (div_le_iff₀ (by positivity : (0 : ℝ) < lambda)).2
      have hlambdaOne : (1 : ℝ) ≤ lambda := by exact_mod_cast hlambda
      exact (mul_le_mul_of_nonneg_left
        (hgammaHalf.trans (by norm_num : (1 / 2 : ℝ) ≤ 1)) halpha.le).trans
          (mul_le_mul_of_nonneg_left hlambdaOne halpha.le)
    norm_num [delta, alpha, simpleNibbleAlpha] at haLe ⊢
    linarith
  have hjobRate0 := hret0
  have hslotRate0 : 0 ≤ fixedSlackSlotRetention
      (variableSlackA alpha gamma lambda) gamma * (1 - gamma) +
        3 * variableSlackEta alpha gamma lambda := by
    have h := variableSlack_slotRetention_pos halpha hgamma0 hgammaHalf
      hlambda (by linarith : alpha ≤ 1)
    linarith
  have htraceGeom :
      (1 - (1 - delta) * variableSlackA alpha gamma lambda / 8) ^ steps ≤
        traceEps := by
    simpa [delta, steps] using variableSlack_geometric_pow_steps_le
      halpha (by linarith : alpha ≤ 1) hgamma0
      (hgammaHalf.trans (by norm_num)) htraceEps0 htraceEps1 hlambda
  have hboundaryPalette : (((L + 1) * (K - 1) : ℕ) : ℝ) ≤
      traceEps * palette := by
    have hnat : (L + 1) * (K - 1) ≤
        dyadicSimpleEndpointBlockScale (L + 1) m := by
      dsimp [K, dyadicSimpleEndpointBlockScale]
      apply Nat.mul_le_mul_left
      simpa using (Nat.sub_le (m ^ 16) 1)
    have hnatR : ((((L + 1) * (K - 1) : ℕ) : ℝ)) ≤
        dyadicSimpleEndpointBlockScale (L + 1) m := by exact_mod_cast hnat
    exact hnatR.trans (hboundary.trans
      (mul_le_mul_of_nonneg_left (by exact_mod_cast hpaletteLower)
        htraceEps0.le))
  have htraceBudget :
      (1 - (1 - delta) * variableSlackA alpha gamma lambda / 8) ^ steps *
            (palette : ℝ) + (((L + 1) * (K - 1) : ℕ) : ℝ) ≤
        eps * palette := by
    have hgeom := mul_le_mul_of_nonneg_right htraceGeom
      (show (0 : ℝ) ≤ palette by positivity)
    dsimp [traceEps] at hgeom hboundaryPalette ⊢
    linarith
  have hreserveSmall : (reserve : ℝ) ≤ eps * palette := by
    have hmR : (1 : ℝ) ≤ m := by exact_mod_cast hm
    have hm17 : (m : ℝ) ^ 17 ≤ (m : ℝ) ^ 20 :=
      pow_le_pow_right₀ hmR (by omega)
    have hres : (reserve : ℝ) = (m : ℝ) ^ 16 := by
      simp [reserve, dyadicSimpleReserveScale]
    rw [hres]
    calc
      (m : ℝ) ^ 16 ≤ (eps * m) * (m : ℝ) ^ 16 := by
        simpa using (mul_le_mul_of_nonneg_right hdecoderGrowth
          (show 0 ≤ (m : ℝ) ^ 16 by positivity))
      _ = eps * (m : ℝ) ^ 17 := by ring
      _ ≤ eps * (m : ℝ) ^ 20 := mul_le_mul_of_nonneg_left hm17 heps0.le
      _ ≤ eps * palette :=
        mul_le_mul_of_nonneg_left (by exact_mod_cast hpaletteLower) heps0.le
  have hone : 1 ≤ eps * palette := by
    have hm20Nat : m ≤ m ^ 20 := by
      calc
        m = m ^ 1 := by simp
        _ ≤ m ^ 20 := Nat.pow_le_pow_right (by omega) (by omega)
    exact hdecoderGrowth.trans (mul_le_mul_of_nonneg_left
      (by exact_mod_cast (show m ≤ palette from
        hm20Nat.trans hpaletteLower)) heps0.le)
  have hbetaSmall : beta ≤ eps * palette := hbeta1.trans hone
  obtain ⟨R0⟩ := G.exists_uniformRealization_family_of_localPacking
    (β := beta) (q := q) (r := r) (hβ := hbeta0) (hr := hrpos)
    hn hpack hs hs1 hqpos
  obtain ⟨P, color, hfeasible, hresidual⟩ :=
    have hgapCall : (S0 : ℝ) ≤ (1 - gamma) * ((N : ℝ) - C) := by
      simpa [d0, Nat.cast_sub hCN] using hgap0
    G.exists_partialColoring_of_selectedBlockDyadicClosedIteration R0
      hB hk hn hs hspos hs1 hq hr0 hr1 hleft homega0 homega1 hrho hrs
      hrhoKappa hpack (hjoint B hjointPalette)
      (hordinary B hordPalette) hordinarySlotCap hreserve
      hextraGamma0 hextraGammaHalf hextraSlotCap hsupportE hchoiceCap
      hordinaryJobCodegree hordinaryPair hextraCodegree hCN hNC
      hdyadicCover hdyadicTop halpha halphaSmall hgamma0 hgammaHalf
      hdelta0 hdelta1 hK hlambda htheta1 hjobRate0 hslotRate0 hgapCall
      hmargin
      (fun n hnstep ↦ (hroundScales n hnstep).degree_five)
      hnextPositive
      (fun n hnstep ↦ (hroundScales n hnstep).endpointBlock_le_degree)
      (fun n hnstep ↦ (hroundScales n hnstep).localScale)
      (fun n hnstep ↦ (hroundScales n hnstep).groupScale)
      (fun n hnstep ↦ (hroundScales n hnstep).slotScale)
      (fun n hnstep ↦ (hroundScales n hnstep).jobScale)
      (fun n hnstep ↦ (hroundScales n hnstep).blockScale)
      haSmall (fun n hnstep ↦ (hroundScales n hnstep).squareScale)
      htraceBudget heps0.le
      (by
        have hcand0 : 0 ≤ extendedProfileCandidateCapacityColumnBound
            (B * k) beta q r := by
          unfold extendedProfileCandidateCapacityColumnBound
          have hdiv0 : 0 ≤
              (explicitLargeSlotBound beta q r : ℝ) / beta :=
            div_nonneg (Nat.cast_nonneg _) hbeta0.le
          positivity
        have hvar0 : 0 ≤ extendedProfileBlockVarianceColumnBound
            B k beta q r := by
          unfold extendedProfileBlockVarianceColumnBound
          positivity
        have hcolumn0 : 0 ≤
            extendedProfileBlockCombinedColumnBound B k beta q r := by
          unfold extendedProfileBlockCombinedColumnBound
          exact add_nonneg
            (mul_nonneg (Nat.cast_nonneg k) hcand0) hvar0
        have hdev0 : 0 ≤ extendedProfileBlockCombinedDeviation
            rho s omega beta q r B k := by
          unfold extendedProfileBlockCombinedDeviation
            FinitePartialResamplingNumerics.packingDeviation
          have hlog0 := FinitePartialResamplingNumerics.packingLog_nonneg hcolumn0
          positivity
        unfold extendedProfileBlockQuadraticBound
        positivity)
      (by simpa [rho, s, omega, beta, q, r, Nat.cast_mul] using
        (hquad B hquadPalette))
      hrhoLoss hone hreserveSmall hbetaSmall
  have hfinal := mul_le_mul_of_nonneg_right h37eps
    (show (0 : ℝ) ≤ palette by positivity)
  exact ⟨P, color, hfeasible, fun v ↦
    (hresidual v).trans (by simpa [palette, Nat.cast_mul] using hfinal)⟩

/-- The proved partial-rounding theorem implies the coefficient-one
asymptotic Vizing analogue. -/
theorem simpleVizingAsymptotic_proved : SimpleVizingAsymptotic.{u} :=
  simpleVizingAsymptotic_of_paddedPartialRounding
    (simpleUniformPaddedPartialRounding_of_multiple
      simpleUniformMultiplePartialRounding_proved)

end

end WeightedEdgeColoring
