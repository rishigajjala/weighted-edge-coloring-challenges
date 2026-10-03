import WeightedEdgeColoring.SubtwoMixedGraphDyadicEventualEnvelope
import WeightedEdgeColoring.SubtwoMixedGraphMaskedScalarBridge

/-! Construct closed mixed matching scalars from one dyadic growth envelope. -/

namespace WeightedEdgeColoring

open RankThreeOptionSystem.OriginalIterationState

noncomputable section

set_option maxHeartbeats 400000 in
theorem mixedGraph_dyadicClosedScalars_of_envelope
    {β alpha gamma delta traceEps cfrac decayBudget : ℝ}
    {A Ccoef L m : ℕ}
    (hdyadicCover : 1 ≤ dyadicScale β L)
    (hA : 0 < A) (hm : 2 ≤ m)
    (halpha : 0 < alpha) (halphaSmall : alpha ≤ 1 / 100000)
    (halphaDelta : alpha ≤ delta / 96)
    (hgamma0 : 0 < gamma) (hgammaHalf : gamma ≤ 1 / 2)
    (hdelta0 : 0 < delta) (hdelta1 : delta ≤ 1)
    (hdeltaHalf : delta = 1 / 2)
    (htraceEps0 : 0 < traceEps) (htraceEps1 : traceEps ≤ 1)
    (hcfrac : cfrac = Real.exp (-2 * decayBudget) / 4)
    (hdecayBudget : decayBudget = 3 * alpha * gamma *
      variableSlackStepMultiplier alpha gamma traceEps)
    (hclosed : ∀ d lambda : ℕ, 0 < d → 0 < lambda →
      cfrac * dyadicSimpleQuantizationScale m ≤ d →
      d ≤ (m + 1) ^ 30 →
      lambda ≤ dyadicSimpleCodegreeScale A m →
      DyadicSimpleClosedRoundScales 1 m d lambda alpha gamma delta)
    (hloss : (Ccoef : ℝ) + 1 ≤ gamma * m)
    (hmarginGrowth : 4 * (1 - gamma) * A ≤
      alpha * gamma ^ 2 * cfrac * m)
    (hfloorGrowth :
      (variableSlackStepMultiplier alpha gamma traceEps) * A ≤
        Real.exp (-2 * decayBudget) / 4 * m) :
    let N := dyadicSimpleQuantizationScale m
    let C := Ccoef * m ^ 20
    let d0 := N - C
    let S0 := fixedSlackPaddedSlotTarget gamma d0
    let lambda := dyadicSimpleCodegreeScale A m
    let K := dyadicSimpleEndpointBlockScale 1 m
    let steps := variableSlackSteps alpha gamma traceEps lambda
    MixedMaskedClosedScalars β alpha gamma delta N C S0 lambda L K steps ∧
      (1 - (1 - delta) * variableSlackA alpha gamma lambda / 8) ^
        steps ≤ traceEps := by
  let N := dyadicSimpleQuantizationScale m
  let C := Ccoef * m ^ 20
  let d0 := N - C
  let S0 := fixedSlackPaddedSlotTarget gamma d0
  let lambda := dyadicSimpleCodegreeScale A m
  let K := dyadicSimpleEndpointBlockScale 1 m
  let steps := variableSlackSteps alpha gamma traceEps lambda
  let T := variableSlackStepMultiplier alpha gamma traceEps
  have halphaOne : alpha ≤ 1 := halphaSmall.trans (by norm_num)
  have halphaSixth : alpha ≤ 1 / 6 := halphaSmall.trans (by norm_num)
  have hcfrac0 : 0 < cfrac := by rw [hcfrac]; positivity
  have hN : 0 < N := by
    dsimp [N]
    exact (dyadicSimple_scales_pos m (by omega)).2.1
  have hlambda : 0 < lambda := by
    dsimp [lambda, dyadicSimpleCodegreeScale]
    exact Nat.mul_pos hA (pow_pos (by omega) _)
  have hK : 0 < K := by
    dsimp [K, dyadicSimpleEndpointBlockScale]
    positivity
  have hlossReal : (C : ℝ) + 1 ≤ gamma * N := by
    have hmR : (1 : ℝ) ≤ m := by
      exact_mod_cast (show 1 ≤ m by omega)
    have hm20 : (1 : ℝ) ≤ (m : ℝ) ^ 20 := one_le_pow₀ hmR
    have hm10 : (m : ℝ) ≤ (m : ℝ) ^ 10 := by
      calc
        (m : ℝ) = (m : ℝ) ^ 1 := by ring
        _ ≤ (m : ℝ) ^ 10 := pow_le_pow_right₀ hmR (by omega)
    have hgrowth : (Ccoef : ℝ) + 1 ≤
        gamma * (m : ℝ) ^ 10 :=
      hloss.trans (mul_le_mul_of_nonneg_left hm10 hgamma0.le)
    dsimp [C, N, dyadicSimpleQuantizationScale]
    push_cast
    calc
      (Ccoef : ℝ) * (m : ℝ) ^ 20 + 1 ≤
          (Ccoef : ℝ) * (m : ℝ) ^ 20 + 1 * (m : ℝ) ^ 20 := by
        convert add_le_add_left hm20 ((Ccoef : ℝ) * (m : ℝ) ^ 20) using 1 <;> ring
      _ = ((Ccoef : ℝ) + 1) * (m : ℝ) ^ 20 := by ring
      _ ≤ (gamma * (m : ℝ) ^ 10) * (m : ℝ) ^ 20 :=
        mul_le_mul_of_nonneg_right hgrowth (by positivity)
      _ = gamma * (m : ℝ) ^ 30 := by ring
  have hCN : C ≤ N := by
    have hiterOne : gamma ≤ 1 :=
      hgammaHalf.trans (by norm_num)
    have hreal : (C : ℝ) ≤ N := by
      calc
        (C : ℝ) ≤ (C : ℝ) + 1 := le_add_of_nonneg_right zero_le_one
        _ ≤ gamma * N := hlossReal
        _ ≤ 1 * (N : ℝ) :=
          mul_le_mul_of_nonneg_right hiterOne (Nat.cast_nonneg N)
        _ = N := one_mul _
    exact_mod_cast hreal
  have hNC : 0 < N - C := by
    have hiterStrict : gamma < 1 :=
      hgammaHalf.trans_lt (by norm_num)
    have hN0 : (0 : ℝ) < N := by exact_mod_cast hN
    apply Nat.sub_pos_of_lt
    exact_mod_cast (show (C : ℝ) < N by
      calc
        (C : ℝ) < (C : ℝ) + 1 := lt_add_one _
        _ ≤ gamma * N := hlossReal
        _ < 1 * (N : ℝ) := mul_lt_mul_of_pos_right hiterStrict hN0
        _ = N := one_mul _)
  have hgapInitial : (S0 : ℝ) ≤ (1 - gamma) * d0 := by
    dsimp [S0, fixedSlackPaddedSlotTarget]
    exact Nat.floor_le (mul_nonneg (by linarith) (Nat.cast_nonneg d0))
  have hret0 : 0 ≤ fixedSlackJobRetention
      (variableSlackA alpha gamma lambda) gamma -
        variableSlackEta alpha gamma lambda :=
    (variableSlack_jobRetention_pos halpha hgamma0
      hgammaHalf hlambda halphaOne).le
  have hretHalf : 1 / 2 ≤ fixedSlackJobRetention
      (variableSlackA alpha gamma lambda) gamma -
        variableSlackEta alpha gamma lambda :=
    variableSlack_half_le_jobRetention halpha.le halphaSixth
      hgamma0.le (hgammaHalf.trans (by norm_num)) hlambda
  have hret1 : fixedSlackJobRetention
      (variableSlackA alpha gamma lambda) gamma -
        variableSlackEta alpha gamma lambda ≤ 1 :=
    variableSlack_jobRetention_le_one halpha.le hgamma0.le
      (hgammaHalf.trans (by norm_num)) hlambda
  have hstepsCast : (steps : ℝ) ≤ T * lambda := by
    simpa [steps, T] using variableSlackSteps_cast_le halpha hgamma0
      htraceEps0 htraceEps1 hlambda
  have hdecay :
      (1 - (fixedSlackJobRetention
          (variableSlackA alpha gamma lambda) gamma -
        variableSlackEta alpha gamma lambda)) * steps ≤ decayBudget := by
    simpa [hdecayBudget, T] using variableSlack_jobDecay_mul_steps_le
      halpha.le hgamma0.le
      (hgammaHalf.trans (by norm_num)) hlambda hstepsCast
  have hfloorSteps : (steps : ℝ) ≤
      Real.exp (-2 * decayBudget) * (1 / 2 : ℝ) * N / 2 := by
    have hmR : (1 : ℝ) ≤ m := by
      exact_mod_cast (show 1 ≤ m by omega)
    have hlambdaCast : (lambda : ℝ) = (A : ℝ) * (m : ℝ) ^ 14 := by
      simp [lambda, dyadicSimpleCodegreeScale]
    have hm16 : (m : ℝ) ≤ (m : ℝ) ^ 16 := by
      calc
        (m : ℝ) = (m : ℝ) ^ 1 := by ring
        _ ≤ (m : ℝ) ^ 16 := pow_le_pow_right₀ hmR (by omega)
    have hTA : T * A ≤ Real.exp (-2 * decayBudget) / 4 * (m : ℝ) ^ 16 :=
      hfloorGrowth.trans (mul_le_mul_of_nonneg_left
        hm16 (by positivity))
    calc
      (steps : ℝ) ≤ T * lambda := hstepsCast
      _ = (T * A) * (m : ℝ) ^ 14 := by rw [hlambdaCast]; ring
      _ ≤ (Real.exp (-2 * decayBudget) / 4 * (m : ℝ) ^ 16) *
          (m : ℝ) ^ 14 := by gcongr
      _ = Real.exp (-2 * decayBudget) * (1 / 2 : ℝ) * N / 2 := by
        simp [N, dyadicSimpleQuantizationScale]
        ring
  have hd0Half : (1 / 2 : ℝ) * N ≤ d0 := by
    have hCHalf : (C : ℝ) ≤ (1 / 2 : ℝ) * N := by
      calc
        (C : ℝ) ≤ (C : ℝ) + 1 := le_add_of_nonneg_right zero_le_one
        _ ≤ gamma * N := hlossReal
        _ ≤ (1 / 2 : ℝ) * N :=
          mul_le_mul_of_nonneg_right hgammaHalf (Nat.cast_nonneg N)
    dsimp [d0]
    rw [Nat.cast_sub hCN]
    apply (le_sub_iff_add_le).2
    calc
      (1 / 2 : ℝ) * N + C ≤
          (1 / 2 : ℝ) * N + (1 / 2 : ℝ) * N :=
        by
          simpa [add_comm] using
            (add_le_add_left hCHalf ((1 / 2 : ℝ) * N))
      _ = N := by ring
  have hdegreeFraction : ∀ t ≤ steps,
      cfrac * N ≤
        RankThreeOptionSystem.OriginalIterationState.naturalSharpJobScale
          d0 (variableSlackA alpha gamma lambda) gamma
          (variableSlackEta alpha gamma lambda) t := by
    have hfrac :=
      RankThreeOptionSystem.OriginalIterationState.naturalSharpJobScale_uniform_fraction
        d0 N steps
          (variableSlackA alpha gamma lambda) gamma
          (variableSlackEta alpha gamma lambda) (1 / 2) decayBudget
          hret0 hretHalf hret1 (by norm_num) hd0Half hdecay hfloorSteps
    intro t ht
    have h := hfrac t ht
    rw [hcfrac]
    convert h using 1; ring
  have hdegreeUpper : ∀ t,
      RankThreeOptionSystem.OriginalIterationState.naturalSharpJobScale
          d0 (variableSlackA alpha gamma lambda) gamma
          (variableSlackEta alpha gamma lambda) t ≤ (m + 1) ^ 30 := by
    intro t
    exact (RankThreeOptionSystem.OriginalIterationState.naturalSharpJobScale_le_initial
      d0 t
        (variableSlackA alpha gamma lambda) gamma
        (variableSlackEta alpha gamma lambda) hret0 hret1).trans
      ((Nat.sub_le N C).trans (Nat.pow_le_pow_left (Nat.le_succ m) 30))
  have hroundScales : ∀ t < steps,
      DyadicSimpleClosedRoundScales 1 m
        (RankThreeOptionSystem.OriginalIterationState.naturalSharpJobScale
          d0 (variableSlackA alpha gamma lambda) gamma
          (variableSlackEta alpha gamma lambda) t)
        lambda alpha gamma delta := by
    intro t ht
    apply hclosed
    · have hd := hdegreeFraction t (Nat.le_of_lt ht)
      have hN0 : (0 : ℝ) < N := by exact_mod_cast hN
      exact_mod_cast (mul_pos hcfrac0 hN0).trans_le hd
    · exact hlambda
    · exact hdegreeFraction t (Nat.le_of_lt ht)
    · exact hdegreeUpper t
    · exact le_rfl
  have hmarginDegree : ∀ t < steps,
      4 * (1 - gamma) ≤
        variableSlackA alpha gamma lambda * gamma *
          RankThreeOptionSystem.OriginalIterationState.naturalSharpJobScale
            d0 (variableSlackA alpha gamma lambda) gamma
            (variableSlackEta alpha gamma lambda) t := by
    intro t ht
    let d := RankThreeOptionSystem.OriginalIterationState.naturalSharpJobScale
      d0 (variableSlackA alpha gamma lambda) gamma
      (variableSlackEta alpha gamma lambda) t
    have hd := hdegreeFraction t (Nat.le_of_lt ht)
    have hlambdaCast : (lambda : ℝ) = (A : ℝ) * (m : ℝ) ^ 14 := by
      simp [lambda, dyadicSimpleCodegreeScale]
    have hmR : (1 : ℝ) ≤ m := by
      exact_mod_cast (show 1 ≤ m by omega)
    have hgrowth : 4 * (1 - gamma) * (lambda : ℝ) ≤
        alpha * gamma ^ 2 * (cfrac * N) := by
      rw [hlambdaCast]
      calc
        4 * (1 - gamma) * ((A : ℝ) * (m : ℝ) ^ 14) =
            (4 * (1 - gamma) * A) * (m : ℝ) ^ 14 := by ring
        _ ≤ (alpha * gamma ^ 2 * cfrac * m) *
            (m : ℝ) ^ 14 := by gcongr
        _ = alpha * gamma ^ 2 * cfrac * (m : ℝ) ^ 15 := by ring
        _ ≤ alpha * gamma ^ 2 * cfrac * (m : ℝ) ^ 30 := by
          exact mul_le_mul_of_nonneg_left
            (pow_le_pow_right₀ hmR (by omega : 15 ≤ 30)) (by positivity)
        _ = alpha * gamma ^ 2 * (cfrac * N) := by
          simp [N, dyadicSimpleQuantizationScale]
          ring
    have hright := mul_le_mul_of_nonneg_left hd
      (show 0 ≤ alpha * gamma ^ 2 by positivity)
    change 4 * (1 - gamma) ≤
      variableSlackA alpha gamma lambda * gamma * (d : ℝ)
    unfold variableSlackA
    rw [show (alpha * gamma / (lambda : ℝ)) * gamma *
        (d : ℝ) = (alpha * gamma ^ 2 * d) / lambda by ring]
    exact (le_div_iff₀ (by positivity : (0 : ℝ) < lambda)).2
      (hgrowth.trans hright)
  have hmargin : ∀ t < steps, 1 - gamma ≤
      (variableSlackA alpha gamma lambda * gamma *
          (1 - gamma) -
        ((1 - gamma) * variableSlackEta alpha gamma lambda +
          3 * variableSlackEta alpha gamma lambda)) *
        RankThreeOptionSystem.OriginalIterationState.naturalSharpJobScale
          d0 (variableSlackA alpha gamma lambda) gamma
          (variableSlackEta alpha gamma lambda) t := by
    intro t ht
    exact variableSlack_iterationMargin_of_degree halpha.le
      hgamma0.le hgammaHalf hlambda (hmarginDegree t ht)
  have hnextPositive : ∀ t < steps,
      0 < (fixedSlackJobRetention
          (variableSlackA alpha gamma lambda) gamma -
        variableSlackEta alpha gamma lambda) *
        RankThreeOptionSystem.OriginalIterationState.naturalSharpJobScale
          d0 (variableSlackA alpha gamma lambda) gamma
          (variableSlackEta alpha gamma lambda) t := by
    intro t ht
    exact mul_pos (lt_of_lt_of_le (by norm_num) hretHalf)
      (by exact_mod_cast (hroundScales t ht).degree_five.trans' (by omega))
  have haLe : variableSlackA alpha gamma lambda ≤ alpha := by
    unfold variableSlackA
    apply (div_le_iff₀ (by positivity : (0 : ℝ) < lambda)).2
    have hlambdaOne : (1 : ℝ) ≤ lambda := by exact_mod_cast hlambda
    exact (mul_le_mul_of_nonneg_left
      (hgammaHalf.trans (by norm_num : (1 / 2 : ℝ) ≤ 1))
        halpha.le).trans (mul_le_mul_of_nonneg_left hlambdaOne halpha.le)
  have htheta1 :
      (1 - delta) * variableSlackA alpha gamma lambda / 8 ≤ 1 := by
    have hdeltaLe : 0 ≤ 1 - delta := by linarith
    have hdeltaOne : 1 - delta ≤ 1 := by linarith
    have ha0 : 0 ≤ variableSlackA alpha gamma lambda := by
      unfold variableSlackA
      positivity
    nlinarith [mul_nonneg hdeltaLe ha0]
  have haSmall : variableSlackA alpha gamma lambda ≤ delta / 96 :=
    haLe.trans halphaDelta
  have hslotRate0 : 0 ≤ fixedSlackSlotRetention
      (variableSlackA alpha gamma lambda) gamma *
        (1 - gamma) +
      3 * variableSlackEta alpha gamma lambda := by
    have h := variableSlack_slotRetention_pos halpha hgamma0
      hgammaHalf hlambda halphaOne
    calc
      0 ≤ fixedSlackSlotRetention
          (variableSlackA alpha gamma lambda) gamma *
            (1 - gamma) +
          2 * variableSlackEta alpha gamma lambda +
          variableSlackEta alpha gamma lambda := h.le
      _ = _ := by ring
  have htraceGeom :
      (1 - (1 - delta) * variableSlackA alpha gamma lambda / 8) ^
          steps ≤ traceEps := by
    simpa [hdeltaHalf, steps] using variableSlack_geometric_pow_steps_le
      halpha halphaOne hgamma0
      (hgammaHalf.trans (by norm_num)) htraceEps0 htraceEps1 hlambda
  have numeric : MixedMaskedClosedScalars β alpha gamma delta
      N C S0 lambda L K steps := by
    have hgapReal : (S0 : ℝ) ≤ (1 - gamma) * ((N : ℝ) - C) := by
      simpa [d0, Nat.cast_sub hCN] using hgapInitial
    exact mixedMaskedClosedScalars_of_dyadicRounds β alpha gamma delta
      N C S0 lambda L steps 1 m hdyadicCover halpha halphaSmall
      hgamma0 hgammaHalf hdelta0 hdelta1 hK hlambda htheta1
      hret0 hslotRate0 hgapReal hmargin hnextPositive haSmall
      hroundScales
  exact ⟨numeric, htraceGeom⟩

end

end WeightedEdgeColoring
