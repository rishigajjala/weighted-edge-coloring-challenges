import WeightedEdgeColoring.RankThreeIsolatedVariableSlack
import WeightedEdgeColoring.RankThreeIsolatedSharpConcreteRound
import Mathlib.Order.Filter.AtTopBot.Group
import Mathlib.Data.Nat.Find

/-!
# Polynomial scales for the simple-graph application

Writing the outer parameter as `m` avoids fractional powers:

* palette: `m^20`;
* quantized job degree: `m^30`;
* local extra reserve: `m^16`;
* codegree cap: a fixed multiple of `m^14`.

Thus the floor loss is `O(m^20)`, the codegree-square ratio has two powers
of `m` to spare, and the endpoint block size is `o(m^20)`.
-/

namespace WeightedEdgeColoring

noncomputable section

open RankThreeOptionSystem

def dyadicSimplePaletteScale (m : ℕ) : ℕ := m ^ 20
def dyadicSimpleQuantizationScale (m : ℕ) : ℕ := m ^ 30
def dyadicSimpleReserveScale (m : ℕ) : ℕ := m ^ 16
def dyadicSimpleCodegreeScale (A m : ℕ) : ℕ := A * m ^ 14
def dyadicSimpleFloorScale (A m : ℕ) : ℕ := A * m ^ 20

/-- The largest integer whose twentieth power is at most the palette. -/
def dyadicSimpleRoot (n : ℕ) : ℕ :=
  Nat.findGreatest (fun m ↦ m ^ 20 ≤ n) n

theorem dyadicSimpleRoot_pow_le (n : ℕ) :
    dyadicSimpleRoot n ^ 20 ≤ n := by
  simpa [dyadicSimpleRoot] using
    (Nat.findGreatest_spec (P := fun m ↦ m ^ 20 ≤ n)
      (Nat.zero_le n) (by simp : 0 ^ 20 ≤ n))

theorem lt_succ_dyadicSimpleRoot_pow (n : ℕ) :
    n < (dyadicSimpleRoot n + 1) ^ 20 := by
  apply lt_of_not_ge
  intro hpow
  have hpos : 0 < dyadicSimpleRoot n + 1 := Nat.succ_pos _
  have hself : dyadicSimpleRoot n + 1 ≤ (dyadicSimpleRoot n + 1) ^ 20 := by
    calc
      dyadicSimpleRoot n + 1 = (dyadicSimpleRoot n + 1) ^ 1 := by simp
      _ ≤ (dyadicSimpleRoot n + 1) ^ 20 := Nat.pow_le_pow_right hpos (by omega)
  have hleN : dyadicSimpleRoot n + 1 ≤ n := hself.trans hpow
  have hmax : dyadicSimpleRoot n + 1 ≤ dyadicSimpleRoot n := by
    simpa [dyadicSimpleRoot] using
      (Nat.le_findGreatest (P := fun m ↦ m ^ 20 ≤ n) hleN hpow)
  omega

theorem le_dyadicSimpleRoot_of_pow_le {M n : ℕ} (h : M ^ 20 ≤ n) :
    M ≤ dyadicSimpleRoot n := by
  have hMn : M ≤ n := by
    by_cases hM : M = 0
    · simp [hM]
    · have hMpos : 0 < M := Nat.pos_iff_ne_zero.mpr hM
      have hMpow : M ≤ M ^ 20 := by
        calc
          M = M ^ 1 := by simp
          _ ≤ M ^ 20 := Nat.pow_le_pow_right hMpos (by omega)
      exact hMpow.trans h
  exact Nat.le_findGreatest hMn h

theorem dyadicSimple_scales_pos (m : ℕ) (hm : 0 < m) :
    0 < dyadicSimplePaletteScale m ∧
    0 < dyadicSimpleQuantizationScale m ∧
    0 < dyadicSimpleReserveScale m := by
  simp [dyadicSimplePaletteScale, dyadicSimpleQuantizationScale,
    dyadicSimpleReserveScale, hm]

theorem dyadicSimple_quantization_div_reserve_cast
    (m : ℕ) (hm : 0 < m) :
    (dyadicSimpleQuantizationScale m : ℝ) /
        dyadicSimpleReserveScale m = (m : ℝ) ^ 14 := by
  unfold dyadicSimpleQuantizationScale dyadicSimpleReserveScale
  push_cast
  have hm0 : (m : ℝ) ≠ 0 := by exact_mod_cast Nat.ne_of_gt hm
  field_simp

theorem dyadicSimple_extraCodegree_le
    (A m : ℕ) (hA : 0 < A) (hm : 0 < m) :
    (dyadicSimpleQuantizationScale m : ℝ) /
        dyadicSimpleReserveScale m ≤ dyadicSimpleCodegreeScale A m := by
  rw [dyadicSimple_quantization_div_reserve_cast m hm]
  unfold dyadicSimpleCodegreeScale
  push_cast
  have hA1 : (1 : ℝ) ≤ A := by exact_mod_cast hA
  have hm14 : 0 ≤ (m : ℝ) ^ 14 := by positivity
  nlinarith

theorem dyadicSimple_floor_le_quantization
    (A m : ℕ) (hm : 1 ≤ m) (hA : A ≤ m ^ 10) :
    dyadicSimpleFloorScale A m ≤ dyadicSimpleQuantizationScale m := by
  unfold dyadicSimpleFloorScale dyadicSimpleQuantizationScale
  calc
    A * m ^ 20 ≤ m ^ 10 * m ^ 20 := Nat.mul_le_mul_right _ hA
    _ = m ^ 30 := by ring

theorem dyadicSimple_reserve_le_palette (m : ℕ) (hm : 0 < m) :
    dyadicSimpleReserveScale m ≤ dyadicSimplePaletteScale m := by
  unfold dyadicSimpleReserveScale dyadicSimplePaletteScale
  exact Nat.pow_le_pow_right hm (by omega)

/-- The exact scalar condition under which the `O(palette)` floor loss is
absorbed by a `gamma` fraction of the larger quantized degree. -/
theorem dyadicSimple_floor_le_gamma_quantization
    (A m : ℕ) (gamma : ℝ) (hgamma0 : 0 ≤ gamma)
    (hA : (A : ℝ) ≤ gamma * (m : ℝ) ^ 10) :
    (dyadicSimpleFloorScale A m : ℝ) ≤
      gamma * dyadicSimpleQuantizationScale m := by
  unfold dyadicSimpleFloorScale dyadicSimpleQuantizationScale
  push_cast
  have hm20 : 0 ≤ (m : ℝ) ^ 20 := by positivity
  have := mul_le_mul_of_nonneg_right hA hm20
  nlinarith

/-- The stronger extra-slot gap absorbs the base-option floor loss. -/
theorem dyadicSimple_extraGap_absorbs_floor
    (A m : ℕ) (gamma : ℝ)
    (hgamma0 : 0 ≤ gamma) (hgamma1 : gamma ≤ 1 / 2)
    (hfloor : (dyadicSimpleFloorScale A m : ℝ) ≤
      gamma * dyadicSimpleQuantizationScale m) :
    (1 - 2 * gamma) * dyadicSimpleQuantizationScale m ≤
      (1 - gamma) *
        (dyadicSimpleQuantizationScale m - dyadicSimpleFloorScale A m) := by
  have hN0 : (0 : ℝ) ≤ dyadicSimpleQuantizationScale m := by positivity
  have hC0 : (0 : ℝ) ≤ dyadicSimpleFloorScale A m := by positivity
  have hcoef : 0 ≤ 1 - gamma := by linarith
  nlinarith [mul_le_mul_of_nonneg_left hfloor hcoef]

/- Squared-codegree condition on the chosen polynomial scales. -/
set_option maxHeartbeats 800000 in
theorem eventually_dyadicSimple_square_ratio
    (A : ℕ) (alpha gamma : ℝ)
    (halpha : 0 < alpha) (hgamma : 0 < gamma) :
    ∀ᶠ m : ℕ in Filter.atTop, ∀ d lambda : ℕ,
      0 < d → 0 < m →
      lambda ≤ dyadicSimpleCodegreeScale A m →
      dyadicSimpleQuantizationScale m ≤ 2 * d →
      d ≤ (m + 1) ^ 30 →
      (lambda : ℝ) ^ 2 * sharpConcreteMomentUpper d ^ 2 ≤
        variableSlackBeta0 alpha gamma * d := by
  let Ucoef : ℝ := 8 * (30 : ℝ) + 10
  let Bcoef : ℝ := (A : ℝ) * Ucoef
  let beta0 := variableSlackBeta0 alpha gamma
  have hbeta0 : 0 < beta0 := by
    dsimp [beta0, variableSlackBeta0]
    positivity
  have hB0 : 0 ≤ Bcoef := by dsimp [Bcoef, Ucoef]; positivity
  filter_upwards [eventually_mul_log_sq_le_linear Bcoef (beta0 / 2)
      hB0 (half_pos hbeta0), Filter.eventually_ge_atTop (1 : ℕ)]
      with m hlog hm1
  have hm : 0 < m := hm1
  intro d lambda hd _hm hlambda hdLower hdUpper
  have hU := sharpConcreteMomentUpper_le_of_polynomial_growth
    d m 30 hm hdUpper
  have hlambdaR : (lambda : ℝ) ≤ (A : ℝ) * (m : ℝ) ^ 14 := by
    exact_mod_cast hlambda
  have hU0 : 0 ≤ sharpConcreteMomentUpper d :=
    le_trans (by norm_num) (sharpConcreteMomentUpper_one_le d hd)
  have hlog0 : 0 ≤ Real.log ((m : ℝ) + 1) := by
    apply Real.log_nonneg
    exact_mod_cast Nat.succ_le_succ (Nat.zero_le m)
  have hAU : (A : ℝ) * sharpConcreteMomentUpper d ≤
      Bcoef * Real.log ((m : ℝ) + 1) := by
    dsimp [Bcoef, Ucoef]
    simpa [mul_assoc] using
      (mul_le_mul_of_nonneg_left hU (Nat.cast_nonneg A))
  have hAU0 : 0 ≤ (A : ℝ) * sharpConcreteMomentUpper d :=
    mul_nonneg (Nat.cast_nonneg A) hU0
  have hAUsq : ((A : ℝ) * sharpConcreteMomentUpper d) ^ 2 ≤
      (Bcoef * Real.log ((m : ℝ) + 1)) ^ 2 :=
    pow_le_pow_left₀ hAU0 hAU 2
  have hm14 : 0 ≤ (m : ℝ) ^ 14 := by positivity
  have hlambdaSq : (lambda : ℝ) ^ 2 ≤
      ((A : ℝ) * (m : ℝ) ^ 14) ^ 2 :=
    pow_le_pow_left₀ (Nat.cast_nonneg lambda) hlambdaR 2
  have hdLowerR : (dyadicSimpleQuantizationScale m : ℝ) ≤ 2 * d := by
    exact_mod_cast hdLower
  have hm29 : (m : ℝ) ^ 29 ≤ (m : ℝ) ^ 30 := by
    have hmR : (1 : ℝ) ≤ m := by exact_mod_cast hm1
    calc
      (m : ℝ) ^ 29 = (m : ℝ) ^ 29 * 1 := by ring
      _ ≤ (m : ℝ) ^ 29 * m :=
        mul_le_mul_of_nonneg_left hmR (by positivity)
      _ = (m : ℝ) ^ 30 := by ring
  have hmain :
      (lambda : ℝ) ^ 2 * sharpConcreteMomentUpper d ^ 2 ≤
        (m : ℝ) ^ 28 *
          (Bcoef * Real.log ((m : ℝ) + 1)) ^ 2 := by
    calc
      (lambda : ℝ) ^ 2 * sharpConcreteMomentUpper d ^ 2 ≤
          ((A : ℝ) * (m : ℝ) ^ 14) ^ 2 *
            sharpConcreteMomentUpper d ^ 2 :=
        mul_le_mul_of_nonneg_right hlambdaSq (sq_nonneg _)
      _ = (m : ℝ) ^ 28 *
          ((A : ℝ) * sharpConcreteMomentUpper d) ^ 2 := by ring
      _ ≤ (m : ℝ) ^ 28 *
          (Bcoef * Real.log ((m : ℝ) + 1)) ^ 2 :=
        mul_le_mul_of_nonneg_left hAUsq (by positivity)
  calc
    (lambda : ℝ) ^ 2 * sharpConcreteMomentUpper d ^ 2 ≤
        (m : ℝ) ^ 28 *
          (Bcoef * Real.log ((m : ℝ) + 1)) ^ 2 := hmain
    _ ≤ (m : ℝ) ^ 28 * ((beta0 / 2) * m) :=
      mul_le_mul_of_nonneg_left hlog (by positivity)
    _ = (beta0 / 2) * (m : ℝ) ^ 29 := by ring
    _ ≤ (beta0 / 2) * (m : ℝ) ^ 30 :=
      mul_le_mul_of_nonneg_left hm29 (by positivity)
    _ = (beta0 / 2) * (dyadicSimpleQuantizationScale m : ℝ) := by
      unfold dyadicSimpleQuantizationScale
      push_cast
      ring
    _ ≤ (beta0 / 2) * (2 * d) :=
      mul_le_mul_of_nonneg_left hdLowerR (by positivity)
    _ = beta0 * d := by ring

/- On the chosen scales the endpoint block size
`O(lambda * log(d)^2)` is negligible compared with the palette `m^20`. -/
set_option maxHeartbeats 800000 in
theorem eventually_dyadicSimple_endpointBlock_sublinear
    (A : ℕ) (hA : 0 < A) (epsilon : ℝ) (hepsilon : 0 < epsilon) :
    ∀ᶠ m : ℕ in Filter.atTop, ∀ d lambda : ℕ,
      0 < d → lambda ≤ dyadicSimpleCodegreeScale A m →
      d ≤ (m + 1) ^ 30 →
      (sharpEndpointBlockFactor * lambda *
          sharpConcreteMomentOrder d ^ 2 : ℕ) ≤
        epsilon * dyadicSimplePaletteScale m := by
  let Ucoef : ℝ := 8 * (30 : ℝ) + 10
  let Fcoef : ℝ := (sharpEndpointBlockFactor : ℝ) * A
  have hF : 0 < Fcoef := by
    have hAR : (0 : ℝ) < A := by exact_mod_cast hA
    dsimp [Fcoef]
    exact mul_pos (by norm_num [sharpEndpointBlockFactor]) hAR
  have hU0 : 0 ≤ Ucoef := by dsimp [Ucoef]; positivity
  have hepsF : 0 < epsilon / Fcoef := div_pos hepsilon hF
  filter_upwards [eventually_mul_log_sq_le_linear Ucoef
      (epsilon / Fcoef) hU0 hepsF,
      Filter.eventually_ge_atTop (1 : ℕ)] with m hlog hm
  intro d lambda hd hlambda hdUpper
  have hk := sharpConcreteMomentOrder_cast_le d hd
  have hU := sharpConcreteMomentUpper_le_of_polynomial_growth
    d m 30 hm hdUpper
  have hklog : (sharpConcreteMomentOrder d : ℝ) ≤
      Ucoef * Real.log ((m : ℝ) + 1) := hk.trans hU
  have hk0 : (0 : ℝ) ≤ sharpConcreteMomentOrder d := Nat.cast_nonneg _
  have hksq : (sharpConcreteMomentOrder d : ℝ) ^ 2 ≤
      (Ucoef * Real.log ((m : ℝ) + 1)) ^ 2 :=
    pow_le_pow_left₀ hk0 hklog 2
  have hlambdaR : (lambda : ℝ) ≤ (A : ℝ) * (m : ℝ) ^ 14 := by
    exact_mod_cast hlambda
  have hcore : (sharpEndpointBlockFactor : ℝ) * (A : ℝ) *
      sharpConcreteMomentOrder d ^ 2 ≤ epsilon * m := by
    have hsquare := mul_le_mul_of_nonneg_left hksq (le_of_lt hF)
    have hlog' := mul_le_mul_of_nonneg_left hlog (le_of_lt hF)
    change Fcoef * sharpConcreteMomentOrder d ^ 2 ≤ epsilon * m
    calc
      Fcoef * sharpConcreteMomentOrder d ^ 2 ≤
          Fcoef * (Ucoef * Real.log ((m : ℝ) + 1)) ^ 2 := hsquare
      _ ≤ Fcoef * ((epsilon / Fcoef) * m) := hlog'
      _ = epsilon * m := by
        field_simp [hF.ne']
        <;> ring
  have hm14 : 0 ≤ (m : ℝ) ^ 14 := by positivity
  have htotal : (sharpEndpointBlockFactor : ℝ) * lambda *
      sharpConcreteMomentOrder d ^ 2 ≤ epsilon * (m : ℝ) ^ 20 := by
    calc
      (sharpEndpointBlockFactor : ℝ) * lambda *
          sharpConcreteMomentOrder d ^ 2 ≤
        ((sharpEndpointBlockFactor : ℝ) * A *
          sharpConcreteMomentOrder d ^ 2) * (m : ℝ) ^ 14 := by
            have hmul := mul_le_mul_of_nonneg_left hlambdaR
              (mul_nonneg (Nat.cast_nonneg sharpEndpointBlockFactor)
                (sq_nonneg (sharpConcreteMomentOrder d : ℝ)))
            simpa [mul_assoc, mul_left_comm, mul_comm] using hmul
      _ ≤ (epsilon * m) * (m : ℝ) ^ 14 :=
        mul_le_mul_of_nonneg_right hcore hm14
      _ ≤ epsilon * (m : ℝ) ^ 20 := by
        have hmR : (1 : ℝ) ≤ m := by exact_mod_cast hm
        have hm5 : (1 : ℝ) ≤ (m : ℝ) ^ 5 := one_le_pow₀ hmR
        have hm15 : (m : ℝ) ^ 15 ≤ (m : ℝ) ^ 20 := by
          calc
            (m : ℝ) ^ 15 = (m : ℝ) ^ 15 * 1 := by ring
            _ ≤ (m : ℝ) ^ 15 * (m : ℝ) ^ 5 := by gcongr
            _ = (m : ℝ) ^ 20 := by ring
        calc
          (epsilon * m) * (m : ℝ) ^ 14 = epsilon * (m : ℝ) ^ 15 := by ring
          _ ≤ epsilon * (m : ℝ) ^ 20 :=
            mul_le_mul_of_nonneg_left hm15 (le_of_lt hepsilon)
  exact_mod_cast htotal

end

end WeightedEdgeColoring
