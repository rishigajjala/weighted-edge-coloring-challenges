import WeightedEdgeColoring.DyadicSimpleIsolatedScales
import WeightedEdgeColoring.NaturalSharpJobScaleBounds

/-!
# Closed round scales on the simple-graph polynomial regime

The endpoint block width is a fixed multiple of `m^16`.  This is two powers
larger than the codegree scale `m^14`, after the logarithmic moment cost, and
four powers smaller than the palette scale `m^20`.
-/

namespace WeightedEdgeColoring

noncomputable section

/-- Endpoint-block width used by the final simple-graph iteration. -/
def dyadicSimpleEndpointBlockScale (B m : ℕ) : ℕ := B * m ^ 16

theorem isolatedVariableZ_add_one_eq_sharpConcreteMomentUpper (d : ℕ) :
    isolatedVariableZ d + 1 = sharpConcreteMomentUpper d := by
  rfl

/-- Uniform logarithmic envelope for every degree below `(m+1)^30`. -/
theorem eventually_dyadicSimple_sharp_square_le_index :
    ∀ᶠ m : ℕ in Filter.atTop, ∀ d : ℕ,
      0 < d → d ≤ (m + 1) ^ 30 →
      sharpConcreteMomentUpper d ^ 2 ≤ m := by
  let Ucoef : ℝ := 8 * (30 : ℝ) + 10
  have hU0 : 0 ≤ Ucoef := by dsimp [Ucoef]; positivity
  filter_upwards [eventually_mul_log_sq_le_linear Ucoef 1 hU0 (by norm_num),
      Filter.eventually_ge_atTop (1 : ℕ)] with m hlog hm
  intro d hd hdUpper
  have hU := sharpConcreteMomentUpper_le_of_polynomial_growth
    d m 30 hm hdUpper
  have hnonneg : 0 ≤ sharpConcreteMomentUpper d :=
    (sharpConcreteMomentUpper_one_le d hd).trans' (by norm_num)
  have hsquare := pow_le_pow_left₀ hnonneg hU 2
  simpa using hsquare.trans hlog

/-- A fixed real constant is eventually below a positive multiple of the
natural index. -/
theorem eventually_const_le_pos_mul_nat
    (C p : ℝ) (hp : 0 < p) :
    ∀ᶠ m : ℕ in Filter.atTop, C ≤ p * m := by
  filter_upwards [Filter.eventually_ge_atTop (Nat.ceil (C / p))] with m hm
  have hceil : C / p ≤ (Nat.ceil (C / p) : ℕ) := Nat.le_ceil _
  have hmR : ((Nat.ceil (C / p) : ℕ) : ℝ) ≤ m := by exact_mod_cast hm
  have hdiv : C / p ≤ (m : ℝ) := hceil.trans hmR
  have := (div_le_iff₀ hp).mp hdiv
  nlinarith

/-- The old logarithmic envelope controls the group rate for the corrected
round when `K=B*m^16` and `lambda≤A*m^14`. -/
theorem dyadicSimple_groupScale_of_growth
    (A B m d lambda : ℕ) (alpha gamma delta : ℝ)
    (hd : 0 < d) (hm : 1 ≤ m) (hlambda : 0 < lambda)
    (hlambdaUpper : lambda ≤ dyadicSimpleCodegreeScale A m)
    (hlog : sharpConcreteMomentUpper d ^ 2 ≤ m)
    (hgrowth : 64 * (A : ℝ) ≤
      delta ^ 2 * alpha * gamma * B * m) :
    isolatedVariableZ d + 1 ≤
      delta ^ 2 * variableSlackA alpha gamma lambda *
        dyadicSimpleEndpointBlockScale B m / 64 := by
  have hU1 : (1 : ℝ) ≤ sharpConcreteMomentUpper d :=
    sharpConcreteMomentUpper_one_le d hd
  have hUleSq : sharpConcreteMomentUpper d ≤
      sharpConcreteMomentUpper d ^ 2 := by nlinarith
  have hUle : sharpConcreteMomentUpper d ≤ (m : ℝ) := hUleSq.trans hlog
  have hlambdaR : (lambda : ℝ) ≤ A * (m : ℝ) ^ 14 := by
    exact_mod_cast hlambdaUpper
  rw [isolatedVariableZ_add_one_eq_sharpConcreteMomentUpper]
  rw [variableSlack_groupScale_formula hlambda]
  apply (le_div_iff₀ (show (0 : ℝ) < 64 * lambda by positivity)).2
  calc
    sharpConcreteMomentUpper d * (64 * (lambda : ℝ)) ≤
        (m : ℝ) * (64 * ((A : ℝ) * (m : ℝ) ^ 14)) := by gcongr
    _ = (64 * (A : ℝ)) * (m : ℝ) ^ 15 := by ring
    _ ≤ (delta ^ 2 * alpha * gamma * B * m) * (m : ℝ) ^ 15 := by
      exact mul_le_mul_of_nonneg_right hgrowth (by positivity)
    _ = delta ^ 2 * alpha * gamma *
        (dyadicSimpleEndpointBlockScale B m : ℕ) := by
      unfold dyadicSimpleEndpointBlockScale
      push_cast
      ring

/-- The same polynomial gap pays the slot upper-tail rate. -/
theorem dyadicSimple_slotScale_of_growth
    (A m d lambda : ℕ) (alpha gamma c : ℝ)
    (hd : 0 < d) (hm : 1 ≤ m) (hlambda : 0 < lambda)
    (halpha : 0 < alpha) (hgamma : 0 < gamma)
    (hlambdaUpper : lambda ≤ dyadicSimpleCodegreeScale A m)
    (hdLower : c * dyadicSimpleQuantizationScale m ≤ d)
    (hlog : sharpConcreteMomentUpper d ^ 2 ≤ m)
    (hgrowth : 393216 * (A : ℝ) ^ 2 ≤
      alpha * gamma ^ 3 * c * m) :
    isolatedVariableZ d + 1 ≤
      variableSlackEta alpha gamma lambda ^ 2 * d /
        (96 * variableSlackA alpha gamma lambda * lambda) := by
  have hU1 : (1 : ℝ) ≤ sharpConcreteMomentUpper d :=
    sharpConcreteMomentUpper_one_le d hd
  have hUleSq : sharpConcreteMomentUpper d ≤
      sharpConcreteMomentUpper d ^ 2 := by nlinarith
  have hUle : sharpConcreteMomentUpper d ≤ (m : ℝ) := hUleSq.trans hlog
  have hlambdaR : (lambda : ℝ) ≤ A * (m : ℝ) ^ 14 := by
    exact_mod_cast hlambdaUpper
  have hlambdaSq : (lambda : ℝ) ^ 2 ≤
      ((A : ℝ) * (m : ℝ) ^ 14) ^ 2 :=
    pow_le_pow_left₀ (by positivity) hlambdaR 2
  rw [isolatedVariableZ_add_one_eq_sharpConcreteMomentUpper]
  rw [variableSlack_slotRate_formula halpha hgamma hlambda]
  apply (le_div_iff₀ (show (0 : ℝ) < 393216 * (lambda : ℝ) ^ 2 by positivity)).2
  calc
    sharpConcreteMomentUpper d * (393216 * (lambda : ℝ) ^ 2) ≤
        (m : ℝ) *
          (393216 * (((A : ℝ) * (m : ℝ) ^ 14) ^ 2)) := by gcongr
    _ = (393216 * (A : ℝ) ^ 2) * (m : ℝ) ^ 29 := by ring
    _ ≤ (alpha * gamma ^ 3 * c * m) * (m : ℝ) ^ 29 := by
      exact mul_le_mul_of_nonneg_right hgrowth (by positivity)
    _ = alpha * gamma ^ 3 *
        (c * (dyadicSimpleQuantizationScale m : ℕ)) := by
      unfold dyadicSimpleQuantizationScale
      push_cast
      ring
    _ ≤ alpha * gamma ^ 3 * d := by
      exact mul_le_mul_of_nonneg_left hdLower (by positivity)

/-- The slot rate is stronger than the job rate, including its smaller
additive logarithmic term. -/
theorem dyadicSimple_jobScale_of_slotScale
    (d lambda : ℕ) (alpha gamma : ℝ)
    (halpha : 0 < alpha) (hgamma : 0 < gamma) (hlambda : 0 < lambda)
    (hslot : isolatedVariableZ d + 1 ≤
      variableSlackEta alpha gamma lambda ^ 2 * d /
        (96 * variableSlackA alpha gamma lambda * lambda)) :
    isolatedVariableZ d + Real.log 2 ≤
      variableSlackEta alpha gamma lambda ^ 2 * d /
        (16 * variableSlackA alpha gamma lambda * lambda) := by
  have hlog2 : Real.log 2 ≤ 1 := by
    have h := Real.log_le_sub_one_of_pos (show (0 : ℝ) < 2 by norm_num)
    norm_num at h ⊢
    exact h
  rw [variableSlack_slotRate_formula halpha hgamma hlambda] at hslot
  rw [variableSlack_jobRate_formula halpha hgamma hlambda]
  have hright : alpha * gamma ^ 3 * d /
      (393216 * (lambda : ℝ) ^ 2) ≤
      alpha * gamma ^ 3 * d / (65536 * (lambda : ℝ) ^ 2) := by
    have hnum : 0 ≤ alpha * gamma ^ 3 * d := by positivity
    apply div_le_div_of_nonneg_left hnum (by positivity)
    nlinarith [sq_nonneg (lambda : ℝ)]
  linarith

/-- The `m^16` endpoint block absorbs the corrected moment-square cost. -/
theorem dyadicSimple_blockScale_of_growth
    (A B m d lambda : ℕ) (alpha gamma delta : ℝ)
    (hd : 0 < d)
    (hlambdaUpper : lambda ≤ dyadicSimpleCodegreeScale A m)
    (hlog : sharpConcreteMomentUpper d ^ 2 ≤ m)
    (hgrowth : 512 * (A : ℝ) ≤ delta * alpha * gamma * B * m) :
    128 * (lambda : ℝ) * (isolatedVariableMoment d : ℝ) ^ 2 ≤
      delta * alpha * gamma * dyadicSimpleEndpointBlockScale B m := by
  have hk := isolatedVariableMoment_cast_le d hd
  have hU := isolatedVariableMomentUpper_le_two_sharpConcrete d
  have hk0 : (0 : ℝ) ≤ isolatedVariableMoment d := by positivity
  have hcorr0 := isolatedVariableMomentUpper_nonneg d
  have hold0 : 0 ≤ sharpConcreteMomentUpper d :=
    (sharpConcreteMomentUpper_one_le d hd).trans' (by norm_num)
  have hkSq : (isolatedVariableMoment d : ℝ) ^ 2 ≤
      4 * sharpConcreteMomentUpper d ^ 2 := by
    have hchain : (isolatedVariableMoment d : ℝ) ≤
        2 * sharpConcreteMomentUpper d := hk.trans hU
    calc
      (isolatedVariableMoment d : ℝ) ^ 2 ≤
          (2 * sharpConcreteMomentUpper d) ^ 2 :=
        pow_le_pow_left₀ hk0 hchain 2
      _ = 4 * sharpConcreteMomentUpper d ^ 2 := by ring
  have hlambdaR : (lambda : ℝ) ≤ A * (m : ℝ) ^ 14 := by
    exact_mod_cast hlambdaUpper
  calc
    128 * (lambda : ℝ) * (isolatedVariableMoment d : ℝ) ^ 2 ≤
        128 * ((A : ℝ) * (m : ℝ) ^ 14) *
          (4 * sharpConcreteMomentUpper d ^ 2) := by gcongr
    _ = (512 * (A : ℝ) * (m : ℝ) ^ 14) *
          sharpConcreteMomentUpper d ^ 2 := by ring
    _ ≤ (512 * (A : ℝ) * (m : ℝ) ^ 14) * m :=
      mul_le_mul_of_nonneg_left hlog (by positivity)
    _ = (512 * (A : ℝ)) * (m : ℝ) ^ 15 := by ring
    _ ≤ (delta * alpha * gamma * B * m) * (m : ℝ) ^ 15 := by
      exact mul_le_mul_of_nonneg_right hgrowth (by positivity)
    _ = delta * alpha * gamma *
        (dyadicSimpleEndpointBlockScale B m : ℕ) := by
      unfold dyadicSimpleEndpointBlockScale
      push_cast
      ring

/-- Pointwise local-degree scale from the fixed-fraction lower degree. -/
theorem dyadicSimple_localScale_of_growth
    (A m d lambda : ℕ) (gamma c : ℝ)
    (hm : 1 ≤ m)
    (hgamma : 0 < gamma)
    (hlambdaUpper : lambda ≤ dyadicSimpleCodegreeScale A m)
    (hdLower : c * dyadicSimpleQuantizationScale m ≤ d)
    (hgrowth : 1000 * ((A : ℝ) + 1) ≤ gamma * c * m ^ 16) :
    1000 * ((lambda : ℝ) + 1) ≤ gamma * d := by
  have hm14 : (1 : ℝ) ≤ (m : ℝ) ^ 14 := one_le_pow₀ (by exact_mod_cast hm)
  have hlambdaR : (lambda : ℝ) ≤ A * (m : ℝ) ^ 14 := by
    exact_mod_cast hlambdaUpper
  have hone : (1 : ℝ) ≤ (m : ℝ) ^ 14 := hm14
  have hsum : (lambda : ℝ) + 1 ≤ ((A : ℝ) + 1) * (m : ℝ) ^ 14 := by
    nlinarith [mul_le_mul_of_nonneg_left hone (Nat.cast_nonneg A)]
  calc
    1000 * ((lambda : ℝ) + 1) ≤
        1000 * (((A : ℝ) + 1) * (m : ℝ) ^ 14) := by gcongr
    _ ≤ (gamma * c * (m : ℝ) ^ 16) * (m : ℝ) ^ 14 := by
      simpa [mul_assoc] using
        (mul_le_mul_of_nonneg_right hgrowth
          (show 0 ≤ (m : ℝ) ^ 14 by positivity))
    _ = gamma * (c * (dyadicSimpleQuantizationScale m : ℕ)) := by
      unfold dyadicSimpleQuantizationScale
      push_cast
      ring
    _ ≤ gamma * d := mul_le_mul_of_nonneg_left hdLower hgamma.le

/-- Pointwise endpoint-block degree bound. -/
theorem dyadicSimple_endpointBlock_le_degree_of_growth
    (B m d : ℕ) (c : ℝ)
    (hdLower : c * dyadicSimpleQuantizationScale m ≤ d)
    (hgrowth : (B : ℝ) ≤ c * m ^ 14) :
    dyadicSimpleEndpointBlockScale B m ≤ d := by
  have hKreal : (dyadicSimpleEndpointBlockScale B m : ℝ) ≤
      c * dyadicSimpleQuantizationScale m := by
    unfold dyadicSimpleEndpointBlockScale dyadicSimpleQuantizationScale
    push_cast
    have hm16 : 0 ≤ (m : ℝ) ^ 16 := by positivity
    have h := mul_le_mul_of_nonneg_right hgrowth hm16
    nlinarith
  exact_mod_cast hKreal.trans hdLower

/-- The corrected square-ratio hypothesis follows from the same one-power
growth gap. -/
theorem dyadicSimple_corrected_square_of_growth
    (A m d lambda : ℕ) (alpha gamma c : ℝ)
    (hd : 0 < d)
    (halpha : 0 < alpha) (hgamma : 0 < gamma)
    (hlambdaUpper : lambda ≤ dyadicSimpleCodegreeScale A m)
    (hdLower : c * dyadicSimpleQuantizationScale m ≤ d)
    (hlog : sharpConcreteMomentUpper d ^ 2 ≤ m)
    (hgrowth : 4 * (A : ℝ) ^ 2 ≤
      variableSlackBeta0 alpha gamma * c * m) :
    (lambda : ℝ) ^ 2 * isolatedVariableMomentUpper d ^ 2 ≤
      variableSlackBeta0 alpha gamma * d := by
  have hcorr := isolatedVariableMomentUpper_le_two_sharpConcrete d
  have hcorr0 := isolatedVariableMomentUpper_nonneg d
  have hold0 : 0 ≤ sharpConcreteMomentUpper d :=
    (sharpConcreteMomentUpper_one_le d hd).trans' (by norm_num)
  have hcorrSq : isolatedVariableMomentUpper d ^ 2 ≤
      4 * sharpConcreteMomentUpper d ^ 2 := by
    calc
      isolatedVariableMomentUpper d ^ 2 ≤
          (2 * sharpConcreteMomentUpper d) ^ 2 :=
        pow_le_pow_left₀ hcorr0 hcorr 2
      _ = 4 * sharpConcreteMomentUpper d ^ 2 := by ring
  have hlambdaR : (lambda : ℝ) ≤ A * (m : ℝ) ^ 14 := by
    exact_mod_cast hlambdaUpper
  have hlambdaSq : (lambda : ℝ) ^ 2 ≤
      ((A : ℝ) * (m : ℝ) ^ 14) ^ 2 :=
    pow_le_pow_left₀ (by positivity) hlambdaR 2
  calc
    (lambda : ℝ) ^ 2 * isolatedVariableMomentUpper d ^ 2 ≤
        (((A : ℝ) * (m : ℝ) ^ 14) ^ 2) *
          (4 * sharpConcreteMomentUpper d ^ 2) := by gcongr
    _ = (4 * (A : ℝ) ^ 2 * (m : ℝ) ^ 28) *
        sharpConcreteMomentUpper d ^ 2 := by ring
    _ ≤ (4 * (A : ℝ) ^ 2 * (m : ℝ) ^ 28) * m :=
      mul_le_mul_of_nonneg_left hlog (by positivity)
    _ = 4 * (A : ℝ) ^ 2 * (m : ℝ) ^ 29 := by ring
    _ ≤ (variableSlackBeta0 alpha gamma * c * m) *
        (m : ℝ) ^ 29 := by
      exact mul_le_mul_of_nonneg_right hgrowth (by positivity)
    _ = variableSlackBeta0 alpha gamma *
        (c * (dyadicSimpleQuantizationScale m : ℕ)) := by
      unfold dyadicSimpleQuantizationScale
      push_cast
      ring
    _ ≤ variableSlackBeta0 alpha gamma * d := by
      exact mul_le_mul_of_nonneg_left hdLower
        (by unfold variableSlackBeta0; positivity)

/-- All scalar hypotheses required by one closed corrected round. -/
structure DyadicSimpleClosedRoundScales
    (B m d lambda : ℕ) (alpha gamma delta : ℝ) : Prop where
  degree_five : 5 ≤ d
  endpointBlock_le_degree : dyadicSimpleEndpointBlockScale B m ≤ d
  localScale : 1000 * ((lambda : ℝ) + 1) ≤ gamma * d
  groupScale : isolatedVariableZ d + 1 ≤
    delta ^ 2 * variableSlackA alpha gamma lambda *
      dyadicSimpleEndpointBlockScale B m / 64
  slotScale : isolatedVariableZ d + 1 ≤
    variableSlackEta alpha gamma lambda ^ 2 * d /
      (96 * variableSlackA alpha gamma lambda * lambda)
  jobScale : isolatedVariableZ d + Real.log 2 ≤
    variableSlackEta alpha gamma lambda ^ 2 * d /
      (16 * variableSlackA alpha gamma lambda * lambda)
  blockScale : 128 * (lambda : ℝ) *
      (isolatedVariableMoment d : ℝ) ^ 2 ≤
    delta * alpha * gamma * dyadicSimpleEndpointBlockScale B m
  squareScale : (lambda : ℝ) ^ 2 * isolatedVariableMomentUpper d ^ 2 ≤
    variableSlackBeta0 alpha gamma * d

/-- Once the accuracy parameters and polynomial coefficients are fixed,
every degree in a fixed positive fraction of the `m^30` window satisfies
all corrected-round scalar hypotheses. -/
theorem eventually_dyadicSimple_closedRoundScales
    (A B : ℕ) (alpha gamma delta c : ℝ)
    (hA : 0 < A) (hB : 0 < B)
    (halpha : 0 < alpha) (hgamma : 0 < gamma)
    (hdelta : 0 < delta) (hc : 0 < c) :
    ∀ᶠ m : ℕ in Filter.atTop, ∀ d lambda : ℕ,
      0 < d → 0 < lambda →
      c * dyadicSimpleQuantizationScale m ≤ d →
      d ≤ (m + 1) ^ 30 →
      lambda ≤ dyadicSimpleCodegreeScale A m →
      DyadicSimpleClosedRoundScales B m d lambda alpha gamma delta := by
  have hpGroup : 0 < delta ^ 2 * alpha * gamma * B := by positivity
  have hpSlot : 0 < alpha * gamma ^ 3 * c := by positivity
  have hpBlock : 0 < delta * alpha * gamma * B := by positivity
  have hpSquare : 0 < variableSlackBeta0 alpha gamma * c := by
    unfold variableSlackBeta0
    positivity
  have hpLocal : 0 < gamma * c := mul_pos hgamma hc
  filter_upwards [eventually_dyadicSimple_sharp_square_le_index,
      eventually_const_le_pos_mul_nat 5 c hc,
      eventually_const_le_pos_mul_nat (B : ℝ) c hc,
      eventually_const_le_pos_mul_nat (1000 * ((A : ℝ) + 1))
        (gamma * c) hpLocal,
      eventually_const_le_pos_mul_nat (64 * (A : ℝ))
        (delta ^ 2 * alpha * gamma * B) hpGroup,
      eventually_const_le_pos_mul_nat (393216 * (A : ℝ) ^ 2)
        (alpha * gamma ^ 3 * c) hpSlot,
      eventually_const_le_pos_mul_nat (512 * (A : ℝ))
        (delta * alpha * gamma * B) hpBlock,
      eventually_const_le_pos_mul_nat (4 * (A : ℝ) ^ 2)
        (variableSlackBeta0 alpha gamma * c) hpSquare,
      Filter.eventually_ge_atTop (1 : ℕ)] with
      m hlog hfive hK hlocal hgroup hslot hblock hsquare hm
  intro d lambda hd hlambda hdLower hdUpper hlambdaUpper
  have hmR : (1 : ℝ) ≤ m := by exact_mod_cast hm
  have hm_le_pow (k : ℕ) (hk : 0 < k) :
      (m : ℝ) ≤ (m : ℝ) ^ k := by
    calc
      (m : ℝ) = (m : ℝ) ^ 1 := by ring
      _ ≤ (m : ℝ) ^ k := by
        exact pow_le_pow_right₀ hmR (by omega)
  have hfive' : (5 : ℝ) ≤ c * (m : ℝ) ^ 30 :=
    hfive.trans (mul_le_mul_of_nonneg_left (hm_le_pow 30 (by omega)) hc.le)
  have hdLower' : c * (m : ℝ) ^ 30 ≤ d := by
    simpa [dyadicSimpleQuantizationScale] using hdLower
  have hdFiveR : (5 : ℝ) ≤ d := hfive'.trans hdLower'
  have hdFive : 5 ≤ d := by exact_mod_cast hdFiveR
  have hK' : (B : ℝ) ≤ c * (m : ℝ) ^ 14 :=
    hK.trans (mul_le_mul_of_nonneg_left (hm_le_pow 14 (by omega)) hc.le)
  have hlocal' : 1000 * ((A : ℝ) + 1) ≤
      gamma * c * (m : ℝ) ^ 16 :=
    hlocal.trans (mul_le_mul_of_nonneg_left (hm_le_pow 16 (by omega)) hpLocal.le)
  have hlogd := hlog d hd hdUpper
  have hGroupScale := dyadicSimple_groupScale_of_growth
    A B m d lambda alpha gamma delta hd hm hlambda hlambdaUpper hlogd hgroup
  have hSlotScale := dyadicSimple_slotScale_of_growth
    A m d lambda alpha gamma c hd hm hlambda halpha hgamma hlambdaUpper
      hdLower hlogd hslot
  exact
    { degree_five := hdFive
      endpointBlock_le_degree :=
        dyadicSimple_endpointBlock_le_degree_of_growth B m d c hdLower hK'
      localScale := dyadicSimple_localScale_of_growth
        A m d lambda gamma c hm hgamma hlambdaUpper hdLower hlocal'
      groupScale := hGroupScale
      slotScale := hSlotScale
      jobScale := dyadicSimple_jobScale_of_slotScale
        d lambda alpha gamma halpha hgamma hlambda hSlotScale
      blockScale := dyadicSimple_blockScale_of_growth
        A B m d lambda alpha gamma delta hd hlambdaUpper hlogd hblock
      squareScale := dyadicSimple_corrected_square_of_growth
        A m d lambda alpha gamma c hd halpha hgamma hlambdaUpper hdLower
          hlogd hsquare }

/-- The endpoint block is negligible compared with the `m^20` palette. -/
theorem eventually_dyadicSimple_fixedEndpointBlock_sublinear
    (B : ℕ) (epsilon : ℝ) (hepsilon : 0 < epsilon) :
    ∀ᶠ m : ℕ in Filter.atTop,
      (dyadicSimpleEndpointBlockScale B m : ℝ) ≤
        epsilon * dyadicSimplePaletteScale m := by
  filter_upwards [eventually_const_le_pos_mul_nat (B : ℝ) epsilon hepsilon,
      Filter.eventually_ge_atTop (1 : ℕ)] with m hmB hm
  unfold dyadicSimpleEndpointBlockScale dyadicSimplePaletteScale
  push_cast
  have hm3 : (1 : ℝ) ≤ (m : ℝ) ^ 3 := one_le_pow₀ (by exact_mod_cast hm)
  calc
    (B : ℝ) * (m : ℝ) ^ 16 ≤
        (epsilon * m) * (m : ℝ) ^ 16 :=
      mul_le_mul_of_nonneg_right hmB (by positivity)
    _ = epsilon * (m : ℝ) ^ 17 := by ring
    _ ≤ epsilon * (m : ℝ) ^ 20 := by
      calc
        epsilon * (m : ℝ) ^ 17 =
            (epsilon * (m : ℝ) ^ 17) * 1 := by ring
        _ ≤ (epsilon * (m : ℝ) ^ 17) * (m : ℝ) ^ 3 :=
          mul_le_mul_of_nonneg_left hm3 (by positivity)
        _ = epsilon * (m : ℝ) ^ 20 := by ring

end

end WeightedEdgeColoring
