import WeightedEdgeColoring.RankThreeIsolatedSharpFixedSlackRound
import WeightedEdgeColoring.RankThreeSharpConcreteScalarData
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Order.Filter.AtTopBot.Group

/-!
# Scalar discharge for isolation-loss moments

The quadratic isolation-loss envelope leaves one transparent scale
condition.  With `k = ceil (8 log (d+1))`, it is enough that

`lambda * (8 log (d+1) + 1)^2 <= beta * d`

and that the fixed constants satisfy

`18 a^2 + (72a+24) beta <= eta`.

The second theorem derives the scale condition from a quantization scale
`n`, assuming `n*lambda <= d` and polynomial growth of `d` in `n`.
-/

namespace WeightedEdgeColoring

/-- Real upper bound for the chosen logarithmic moment order. -/
noncomputable def sharpConcreteMomentUpper (d : ℕ) : ℝ :=
  8 * Real.log ((d : ℝ) + 1) + 1

theorem sharpConcreteMomentOrder_pos (d : ℕ) (hd : 0 < d) :
    0 < sharpConcreteMomentOrder d := by
  apply Nat.ceil_pos.mpr
  have harg : (1 : ℝ) < (d : ℝ) + 1 := by
    exact_mod_cast Nat.succ_lt_succ hd
  exact mul_pos (by norm_num) (Real.log_pos harg)

/-- Ceiling costs only the displayed additive one. -/
theorem sharpConcreteMomentOrder_cast_le (d : ℕ) (hd : 0 < d) :
    (sharpConcreteMomentOrder d : ℝ) ≤ sharpConcreteMomentUpper d := by
  unfold sharpConcreteMomentOrder sharpConcreteMomentUpper
  have hx0 : 0 ≤ 8 * Real.log ((d : ℝ) + 1) := by
    have harg : (1 : ℝ) ≤ (d : ℝ) + 1 := by
      exact_mod_cast Nat.succ_le_succ (Nat.zero_le d)
    exact mul_nonneg (by norm_num) (Real.log_nonneg harg)
  exact (Nat.ceil_lt_add_one hx0).le

theorem sharpConcreteMomentUpper_one_le (d : ℕ) (hd : 0 < d) :
    (1 : ℝ) ≤ sharpConcreteMomentUpper d := by
  unfold sharpConcreteMomentUpper
  have harg : (1 : ℝ) ≤ (d : ℝ) + 1 := by
    exact_mod_cast Nat.succ_le_succ (Nat.zero_le d)
  have hlog : 0 ≤ Real.log ((d : ℝ) + 1) := Real.log_nonneg harg
  nlinarith

/-- The exact three-budget split behind the scalar condition. -/
theorem isolatedLoss_scaled_of_square_ratio
    (a eta beta : ℝ) (d lambda : ℕ)
    (hd : 0 < d) (hlambda : 0 < lambda)
    (ha0 : 0 ≤ a) (hbeta0 : 0 ≤ beta)
    (hratio : (lambda : ℝ) * sharpConcreteMomentUpper d ^ 2 ≤
      beta * d)
    (hbudget : 18 * a ^ 2 + (72 * a + 24) * beta ≤ eta) :
    18 * a ^ 2 * d +
        72 * a * sharpConcreteMomentOrder d * lambda +
        24 * sharpConcreteMomentOrder d ^ 2 * lambda ≤
      eta * d := by
  let k := sharpConcreteMomentOrder d
  let U := sharpConcreteMomentUpper d
  have hkpos : 0 < k := sharpConcreteMomentOrder_pos d hd
  have hk1R : (1 : ℝ) ≤ k := by exact_mod_cast hkpos
  have hkU : (k : ℝ) ≤ U := sharpConcreteMomentOrder_cast_le d hd
  have hU0 : 0 ≤ U := le_trans (by norm_num)
    (sharpConcreteMomentUpper_one_le d hd)
  have hk0 : (0 : ℝ) ≤ k := by positivity
  have hkSq : (k : ℝ) ^ 2 ≤ U ^ 2 :=
    pow_le_pow_left₀ hk0 hkU 2
  have hlambda0 : (0 : ℝ) ≤ lambda := by positivity
  have hkSqLambda : (k : ℝ) ^ 2 * lambda ≤ beta * d := by
    calc
      (k : ℝ) ^ 2 * lambda ≤ U ^ 2 * lambda := by gcongr
      _ = (lambda : ℝ) * U ^ 2 := by ring
      _ ≤ beta * d := hratio
  have hkLambda : (k : ℝ) * lambda ≤ beta * d := by
    calc
      (k : ℝ) * lambda ≤ (k : ℝ) ^ 2 * lambda := by
        have : (k : ℝ) ≤ (k : ℝ) ^ 2 := by nlinarith
        exact mul_le_mul_of_nonneg_right this hlambda0
      _ ≤ beta * d := hkSqLambda
  have hd0 : (0 : ℝ) ≤ d := by positivity
  have h72a0 : (0 : ℝ) ≤ 72 * a := mul_nonneg (by norm_num) ha0
  have hlinear : 72 * a * (k : ℝ) * lambda ≤
      (72 * a) * (beta * d) := by
    simpa [mul_assoc] using
      (mul_le_mul_of_nonneg_left hkLambda h72a0)
  have hquad : 24 * (k : ℝ) ^ 2 * lambda ≤
      24 * (beta * d) := by
    nlinarith
  have hbudgetD := mul_le_mul_of_nonneg_right hbudget hd0
  dsimp [k] at hkLambda hkSqLambda hlinear hquad ⊢
  push_cast at hlinear hquad ⊢
  nlinarith

/-- Quantized-scale route to the square-ratio hypothesis.  The first
premise says `d/lambda >= n`; the next two say that the logarithmic moment
order is at most `B log(n+1)` and that its square is `o(n)`. -/
theorem sharpConcrete_square_ratio_of_quantized_scale
    (d lambda n : ℕ) (B beta : ℝ)
    (hd : 0 < d) (hn : 0 < n)
    (hscale : n * lambda ≤ d)
    (hB0 : 0 ≤ B) (hbeta0 : 0 ≤ beta)
    (hlogGrowth : sharpConcreteMomentUpper d ≤
      B * Real.log ((n : ℝ) + 1))
    (hlogSquare : (B * Real.log ((n : ℝ) + 1)) ^ 2 ≤ beta * n) :
    (lambda : ℝ) * sharpConcreteMomentUpper d ^ 2 ≤ beta * d := by
  have hlogn0 : 0 ≤ Real.log ((n : ℝ) + 1) := by
    apply Real.log_nonneg
    exact_mod_cast Nat.succ_le_succ (Nat.zero_le n)
  have hU0 : 0 ≤ sharpConcreteMomentUpper d := by
    exact le_trans (by norm_num) (sharpConcreteMomentUpper_one_le d hd)
  have hBlog0 : 0 ≤ B * Real.log ((n : ℝ) + 1) :=
    mul_nonneg hB0 hlogn0
  have hsq : sharpConcreteMomentUpper d ^ 2 ≤
      (B * Real.log ((n : ℝ) + 1)) ^ 2 :=
    pow_le_pow_left₀ hU0 hlogGrowth 2
  have hlambda0 : (0 : ℝ) ≤ lambda := by positivity
  have hscaleR : (n : ℝ) * lambda ≤ d := by exact_mod_cast hscale
  calc
    (lambda : ℝ) * sharpConcreteMomentUpper d ^ 2 ≤
        lambda * (B * Real.log ((n : ℝ) + 1)) ^ 2 := by gcongr
    _ ≤ lambda * (beta * n) := by gcongr
    _ = beta * (n * lambda) := by ring
    _ ≤ beta * d := mul_le_mul_of_nonneg_left hscaleR hbeta0

/-- Ready-to-use quantized corollary for the exact isolation-loss scalar
inequality. -/
theorem isolatedLoss_scaled_of_quantized_scale
    (a eta beta B : ℝ) (d lambda n : ℕ)
    (hd : 0 < d) (hlambda : 0 < lambda) (hn : 0 < n)
    (ha0 : 0 ≤ a) (hbeta0 : 0 ≤ beta) (hB0 : 0 ≤ B)
    (hscale : n * lambda ≤ d)
    (hlogGrowth : sharpConcreteMomentUpper d ≤
      B * Real.log ((n : ℝ) + 1))
    (hlogSquare : (B * Real.log ((n : ℝ) + 1)) ^ 2 ≤ beta * n)
    (hbudget : 18 * a ^ 2 + (72 * a + 24) * beta ≤ eta) :
    18 * a ^ 2 * d +
        72 * a * sharpConcreteMomentOrder d * lambda +
        24 * sharpConcreteMomentOrder d ^ 2 * lambda ≤
      eta * d := by
  apply isolatedLoss_scaled_of_square_ratio a eta beta d lambda
    hd hlambda ha0 hbeta0
  · exact sharpConcrete_square_ratio_of_quantized_scale
      d lambda n B beta hd hn hscale hB0 hbeta0 hlogGrowth hlogSquare
  · exact hbudget

/-! ## Closing the logarithmic scale premise

The next two lemmas remove the last asymptotic premise from the
quantized-scale argument.  The first is the standard fact that a fixed
multiple of `log(n+1)^2` is eventually smaller than every positive
multiple of `n`.  The second gives the concrete logarithmic envelope
used when the current degree is polynomial in the quantization scale.
-/

/-- A fixed squared logarithm is eventually at most any prescribed
positive multiple of `n`.  The shift by one makes the statement valid
without a separate convention at zero. -/
theorem eventually_mul_log_sq_le_linear
    (B beta : ℝ) (_hB0 : 0 ≤ B) (hbeta : 0 < beta) :
    ∀ᶠ n : ℕ in Filter.atTop,
      (B * Real.log ((n : ℝ) + 1)) ^ 2 ≤ beta * n := by
  have hloReal :
      (fun x : ℝ => (B * Real.log x) ^ 2) =o[Filter.atTop]
        (fun x : ℝ => x) := by
    have h :=
      (Real.isLittleO_pow_log_id_atTop (n := 2)).const_mul_left (B ^ 2)
    exact h.congr_left fun x => by ring
  have hshift :
      Filter.Tendsto (fun n : ℕ => (n : ℝ) + 1)
        Filter.atTop Filter.atTop :=
    Filter.tendsto_atTop_add_const_right _ _ tendsto_natCast_atTop_atTop
  have hloNat :
      (fun n : ℕ => (B * Real.log ((n : ℝ) + 1)) ^ 2) =o[Filter.atTop]
        (fun n : ℕ => (n : ℝ) + 1) := by
    simpa [Function.comp_def] using hloReal.comp_tendsto hshift
  filter_upwards [hloNat.bound (half_pos hbeta),
      Filter.eventually_ge_atTop (1 : ℕ)] with n hn hn1
  rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _),
    Real.norm_eq_abs, abs_of_nonneg (by positivity)] at hn
  have hn1R : (1 : ℝ) ≤ n := by exact_mod_cast hn1
  nlinarith

/-- Pointwise threshold form of `eventually_mul_log_sq_le_linear`. -/
theorem exists_mul_log_sq_le_linear
    (B beta : ℝ) (hB0 : 0 ≤ B) (hbeta : 0 < beta) :
    ∃ N : ℕ, ∀ n : ℕ, N ≤ n →
      (B * Real.log ((n : ℝ) + 1)) ^ 2 ≤ beta * n := by
  exact Filter.eventually_atTop.mp
    (eventually_mul_log_sq_le_linear B beta hB0 hbeta)

/-- For positive `n`, the harmless ceiling term `+1` in the moment
order is absorbed by two additional copies of `log(n+1)`. -/
theorem one_le_two_mul_log_nat_add_one (n : ℕ) (hn : 0 < n) :
    (1 : ℝ) ≤ 2 * Real.log ((n : ℝ) + 1) := by
  have hnR : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hden : 0 < (n : ℝ) + 2 := by positivity
  have hhalf : (1 / 2 : ℝ) ≤ 2 * (n : ℝ) / ((n : ℝ) + 2) := by
    apply (le_div_iff₀ hden).2
    nlinarith
  have hseries := Real.le_log_one_add_of_nonneg (show (0 : ℝ) ≤ n by positivity)
  rw [add_comm (1 : ℝ) n] at hseries
  nlinarith

/-- Polynomial growth of the current degree gives the logarithmic
envelope needed by `sharpConcrete_square_ratio_of_quantized_scale`.
The coefficient `8*C+10` includes the ceiling and the `d+1` shift. -/
theorem sharpConcreteMomentUpper_le_of_polynomial_growth
    (d n C : ℕ) (hn : 0 < n) (hpoly : d ≤ (n + 1) ^ C) :
    sharpConcreteMomentUpper d ≤
      (8 * (C : ℝ) + 10) * Real.log ((n : ℝ) + 1) := by
  let x : ℝ := (n : ℝ) + 1
  have hx1 : (1 : ℝ) ≤ x := by
    dsimp [x]
    exact_mod_cast Nat.succ_le_succ (Nat.zero_le n)
  have hxpos : 0 < x := zero_lt_one.trans_le hx1
  have hpow1 : (1 : ℝ) ≤ x ^ C := one_le_pow₀ hx1
  have hpolyR : (d : ℝ) ≤ x ^ C := by
    dsimp [x]
    exact_mod_cast hpoly
  have hdom : (d : ℝ) + 1 ≤ 2 * x ^ C := by nlinarith
  have hd1pos : 0 < (d : ℝ) + 1 := by positivity
  have hlogdom := Real.log_le_log hd1pos hdom
  have hpowne : x ^ C ≠ 0 := pow_ne_zero _ hxpos.ne'
  rw [Real.log_mul (by norm_num : (2 : ℝ) ≠ 0) hpowne,
    Real.log_pow] at hlogdom
  have htwo : (2 : ℝ) ≤ x := by
    dsimp [x]
    exact_mod_cast Nat.succ_le_succ hn
  have hlogTwo : Real.log 2 ≤ Real.log x :=
    Real.log_le_log (by norm_num) htwo
  have hone := one_le_two_mul_log_nat_add_one n hn
  unfold sharpConcreteMomentUpper
  dsimp [x] at hlogdom hlogTwo
  nlinarith

/-- Fully closed square-ratio premise for polynomial quantization:
once `n` is past a fixed threshold, no logarithmic hypothesis remains. -/
theorem eventually_sharpConcrete_square_ratio_of_polynomial_growth
    (C : ℕ) (beta : ℝ) (hbeta : 0 < beta) :
    ∀ᶠ n : ℕ in Filter.atTop, ∀ d lambda : ℕ,
      0 < d → 0 < n → n * lambda ≤ d → d ≤ (n + 1) ^ C →
      (lambda : ℝ) * sharpConcreteMomentUpper d ^ 2 ≤ beta * d := by
  have hB0 : (0 : ℝ) ≤ 8 * (C : ℝ) + 10 := by positivity
  filter_upwards [eventually_mul_log_sq_le_linear
      (8 * (C : ℝ) + 10) beta hB0 hbeta,
      Filter.eventually_ge_atTop (1 : ℕ)] with n hsq hn
  have hnpos : 0 < n := hn
  intro d lambda hd _hn hscale hpoly
  exact sharpConcrete_square_ratio_of_quantized_scale
    d lambda n (8 * (C : ℝ) + 10) beta hd hnpos hscale hB0 hbeta.le
      (sharpConcreteMomentUpper_le_of_polynomial_growth d n C hnpos hpoly) hsq

/-- Eventual, assumption-free discharge of the isolation-loss envelope
in the polynomial quantization regime.  Only the fixed arithmetic
budget remains. -/
theorem eventually_isolatedLoss_scaled_of_polynomial_quantization
    (a eta beta : ℝ) (C : ℕ)
    (ha0 : 0 ≤ a) (hbeta : 0 < beta)
    (hbudget : 18 * a ^ 2 + (72 * a + 24) * beta ≤ eta) :
    ∀ᶠ n : ℕ in Filter.atTop, ∀ d lambda : ℕ,
      0 < d → 0 < lambda → 0 < n →
      n * lambda ≤ d → d ≤ (n + 1) ^ C →
      18 * a ^ 2 * d +
          72 * a * sharpConcreteMomentOrder d * lambda +
          24 * sharpConcreteMomentOrder d ^ 2 * lambda ≤
        eta * d := by
  filter_upwards [eventually_sharpConcrete_square_ratio_of_polynomial_growth
      C beta hbeta] with n hratio
  intro d lambda hd hlambda hn hscale hpoly
  apply isolatedLoss_scaled_of_square_ratio
    a eta beta d lambda hd hlambda ha0 hbeta.le
  · exact hratio d lambda hd hn hscale hpoly
  · exact hbudget

/-- Honest codegree-scaled form of the isolation budget.  When
`a = alpha/lambda` and `eta = a/64`, the logarithmic requirement is on
`lambda^2 * U(d)^2`, not merely on `lambda * U(d)^2`. -/
theorem isolatedLoss_scaled_of_squared_codegree_ratio
    (alpha beta0 : ℝ) (d lambda : ℕ)
    (hd : 0 < d) (hlambda : 0 < lambda)
    (halpha : 0 ≤ alpha) (hbeta0 : 0 ≤ beta0)
    (hratio : (lambda : ℝ) ^ 2 * sharpConcreteMomentUpper d ^ 2 ≤
      beta0 * d)
    (hfixed : 18 * alpha ^ 2 + (72 * alpha + 24) * beta0 ≤
      alpha / 64) :
    18 * (alpha / lambda) ^ 2 * d +
        72 * (alpha / lambda) * sharpConcreteMomentOrder d * lambda +
        24 * sharpConcreteMomentOrder d ^ 2 * lambda ≤
      (alpha / lambda / 64) * d := by
  have hlambdaR : (0 : ℝ) < lambda := by exact_mod_cast hlambda
  have hratio' : (lambda : ℝ) * sharpConcreteMomentUpper d ^ 2 ≤
      (beta0 / lambda) * d := by
    rw [show (beta0 / (lambda : ℝ)) * d = (beta0 * d) / lambda by ring]
    apply (le_div_iff₀ hlambdaR).2
    calc
      (lambda : ℝ) * sharpConcreteMomentUpper d ^ 2 * lambda =
          (lambda : ℝ) ^ 2 * sharpConcreteMomentUpper d ^ 2 := by ring
      _ ≤ beta0 * d := hratio
  have hbudget :
      18 * (alpha / lambda) ^ 2 +
          (72 * (alpha / lambda) + 24) * (beta0 / lambda) ≤
        alpha / lambda / 64 := by
    have hlambda1 : (1 : ℝ) ≤ lambda := by exact_mod_cast hlambda
    have hscaled := div_le_div_of_nonneg_right hfixed hlambdaR.le
    have hfirst : 18 * (alpha / lambda) ^ 2 ≤
        (18 * alpha ^ 2) / lambda := by
      rw [div_pow]
      have hsq : (lambda : ℝ) ≤ lambda ^ 2 := by nlinarith
      have hnum : 0 ≤ 18 * alpha ^ 2 := by positivity
      convert div_le_div_of_nonneg_left hnum hlambdaR hsq using 1 <;> ring
    have hsecond :
        (72 * (alpha / lambda) + 24) * (beta0 / lambda) ≤
          ((72 * alpha + 24) * beta0) / lambda := by
      have haDiv : alpha / lambda ≤ alpha :=
        (div_le_iff₀ hlambdaR).2 (by nlinarith)
      have hcoef : 72 * (alpha / lambda) + 24 ≤ 72 * alpha + 24 := by
        nlinarith
      have h := div_le_div_of_nonneg_right
        (mul_le_mul_of_nonneg_right hcoef hbeta0) hlambdaR.le
      convert h using 1 <;> ring
    calc
      18 * (alpha / lambda) ^ 2 +
          (72 * (alpha / lambda) + 24) * (beta0 / lambda) ≤
        (18 * alpha ^ 2) / lambda +
          ((72 * alpha + 24) * beta0) / lambda := add_le_add hfirst hsecond
      _ = (18 * alpha ^ 2 + (72 * alpha + 24) * beta0) / lambda := by ring
      _ ≤ (alpha / 64) / lambda := hscaled
      _ = alpha / lambda / 64 := by field_simp
  exact isolatedLoss_scaled_of_square_ratio
    (alpha / lambda) (alpha / lambda / 64) (beta0 / lambda)
      d lambda hd hlambda (by positivity) (by positivity) hratio' hbudget

end WeightedEdgeColoring
