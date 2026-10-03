import WeightedEdgeColoring.PackingDeviationAsymptotic

/-!
# Sublinear packing deviation with polynomial columns

The concrete profile selector has a linear row bound but a polynomial
source--state column bound.  Only the logarithm of the column bound enters
the packing deviation.  This file records the uniform numerical statement
needed by that application: for every fixed natural degree `d`,

`R <= A*n` and `C <= C0*n^d`

still imply `packingDeviation R C = o(n)`.
-/

namespace WeightedEdgeColoring.FinitePartialResamplingNumerics

noncomputable section

/-- `packingLog` is monotone on nonnegative column bounds. -/
theorem packingLog_mono {C C' : ℝ} (hC : 0 ≤ C) (hCC' : C ≤ C') :
    packingLog C ≤ packingLog C' := by
  unfold packingLog
  apply Real.log_le_log
  · linarith
  · linarith

/-- A fixed polynomial column bound has logarithm at most a constant plus
`2*d*sqrt n`.  The deliberately coarse square-root estimate is convenient
for the later uniform epsilon argument. -/
theorem packingLog_polynomial_natCast_le
    {C0 : ℝ} (hC0 : 0 ≤ C0) (d : ℕ)
    {n : ℕ} (hn : 1 ≤ n) :
    packingLog (C0 * (n : ℝ) ^ d) ≤
      Real.log (3 + 16 * C0) +
        2 * (d : ℝ) * Real.sqrt (n : ℝ) := by
  let D : ℝ := 3 + 16 * C0
  have hnR : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hnpos : (0 : ℝ) < n := lt_of_lt_of_le zero_lt_one hnR
  have hpow1 : (1 : ℝ) ≤ (n : ℝ) ^ d := one_le_pow₀ hnR
  have hpowpos : (0 : ℝ) < (n : ℝ) ^ d := pow_pos hnpos d
  have hDpos : 0 < D := by dsimp [D]; linarith
  have hinside :
      3 + 16 * (C0 * (n : ℝ) ^ d) ≤ D * (n : ℝ) ^ d := by
    dsimp [D]
    nlinarith
  have hlogn : Real.log (n : ℝ) ≤ 2 * Real.sqrt (n : ℝ) := by
    have h := Real.log_le_rpow_div (Nat.cast_nonneg n)
      (show (0 : ℝ) < 1 / 2 by norm_num)
    rw [← Real.sqrt_eq_rpow] at h
    nlinarith
  calc
    packingLog (C0 * (n : ℝ) ^ d) =
        Real.log (3 + 16 * (C0 * (n : ℝ) ^ d)) := rfl
    _ ≤ Real.log (D * (n : ℝ) ^ d) :=
      Real.log_le_log (by positivity) hinside
    _ = Real.log D + Real.log ((n : ℝ) ^ d) :=
      Real.log_mul hDpos.ne' hpowpos.ne'
    _ = Real.log D + (d : ℝ) * Real.log (n : ℝ) := by
      rw [Real.log_pow]
    _ ≤ Real.log D + (d : ℝ) *
        (2 * Real.sqrt (n : ℝ)) := by
      exact add_le_add_right
        (mul_le_mul_of_nonneg_left hlogn (Nat.cast_nonneg d)) _
    _ = Real.log (3 + 16 * C0) +
        2 * (d : ℝ) * Real.sqrt (n : ℝ) := by
      dsimp [D]
      ring

/-- A version of the deviation estimate in which the actual row and column
parameters need only satisfy a linear row bound and a separately supplied
linear logarithmic bound. -/
theorem packingDeviation_le_of_linear_row_and_log
    {R C A lambda : ℝ} {n : ℕ}
    (hR0 : 0 ≤ R) (hC0 : 0 ≤ C)
    (hA : 0 ≤ A) (hlambda : 0 ≤ lambda)
    (hrow : R ≤ A * n)
    (hlog : packingLog C ≤ lambda * n) :
    packingDeviation R C ≤
      (4 * Real.sqrt (A * lambda) + 4 * lambda) * n := by
  have hn0 : 0 ≤ (n : ℝ) := Nat.cast_nonneg n
  have hL0 : 0 ≤ packingLog C := packingLog_nonneg hC0
  have hprod :
      R * packingLog C ≤ (A * lambda) * (n : ℝ) ^ 2 := by
    calc
      R * packingLog C ≤ (A * n) * (lambda * n) :=
        mul_le_mul hrow hlog hL0 (mul_nonneg hA hn0)
      _ = (A * lambda) * (n : ℝ) ^ 2 := by ring
  have hinside0 : 0 ≤ R * packingLog C := mul_nonneg hR0 hL0
  have hAlambda0 : 0 ≤ A * lambda := mul_nonneg hA hlambda
  have hsqrt0 := Real.sqrt_nonneg (R * packingLog C)
  have hrhs0 : 0 ≤ Real.sqrt (A * lambda) * (n : ℝ) :=
    mul_nonneg (Real.sqrt_nonneg _) hn0
  have hsqrt_sq :
      (Real.sqrt (R * packingLog C)) ^ 2 = R * packingLog C :=
    Real.sq_sqrt hinside0
  have hrhs_sq :
      (Real.sqrt (A * lambda) * (n : ℝ)) ^ 2 =
        (A * lambda) * (n : ℝ) ^ 2 := by
    rw [mul_pow, Real.sq_sqrt hAlambda0]
  have hsqrt :
      Real.sqrt (R * packingLog C) ≤
        Real.sqrt (A * lambda) * n := by
    nlinarith
  unfold packingDeviation
  calc
    4 * Real.sqrt (R * packingLog C) + 4 * packingLog C ≤
        4 * (Real.sqrt (A * lambda) * n) +
          4 * (lambda * n) := by
      gcongr
    _ = (4 * Real.sqrt (A * lambda) + 4 * lambda) * n := by ring

/-- Uniform sublinearity for a linear row bound and any fixed-degree
polynomial column bound.  `R` and `C` may be smaller than the displayed
envelopes; this is the form used by the block selector. -/
theorem packingDeviation_sublinear_of_linear_row_polynomial_column
    {A C0 : ℝ} (hA : 0 ≤ A) (hC0 : 0 ≤ C0) (d : ℕ) :
    ∀ epsilon : ℝ, 0 < epsilon → ∃ N : ℕ, ∀ n : ℕ, N ≤ n →
      ∀ R C : ℝ, 0 ≤ R → 0 ≤ C →
        R ≤ A * n → C ≤ C0 * (n : ℝ) ^ d →
          packingDeviation R C ≤ epsilon * n := by
  intro epsilon hepsilon
  let Abar : ℝ := A + 1
  let lambda : ℝ := min (epsilon ^ 2 / (1024 * Abar)) (epsilon / 16)
  have hAbar : 0 < Abar := by dsimp [Abar]; linarith
  have hlambda : 0 < lambda := by
    dsimp [lambda]
    exact lt_min
      (div_pos (sq_pos_of_pos hepsilon) (mul_pos (by norm_num) hAbar))
      (div_pos hepsilon (by norm_num))
  let D : ℝ := 3 + 16 * C0
  have hD : 0 < D := by dsimp [D]; linarith
  have hlogD0 : 0 ≤ Real.log D := (Real.log_pos (by linarith)).le
  let delta : ℝ := lambda / (4 * ((d : ℝ) + 1))
  have hdelta : 0 < delta := by
    dsimp [delta]
    exact div_pos hlambda (mul_pos (by norm_num) (by positivity))
  let threshold : ℝ := max 1
    (max (1 / delta ^ 2) (2 * Real.log D / lambda))
  let N : ℕ := Nat.ceil threshold
  refine ⟨N, ?_⟩
  intro n hn R C hR0 hC0' hrow hcolumn
  have hthreshold : threshold ≤ (n : ℝ) := by
    calc
      threshold ≤ (N : ℝ) := Nat.le_ceil threshold
      _ ≤ n := by exact_mod_cast hn
  have hn_one_real : (1 : ℝ) ≤ n := by
    exact (le_max_left 1
      (max (1 / delta ^ 2) (2 * Real.log D / lambda))).trans hthreshold
  have hn_one : 1 ≤ n := by exact_mod_cast hn_one_real
  have hn_delta : 1 / delta ^ 2 ≤ (n : ℝ) := by
    exact (le_max_left (1 / delta ^ 2) (2 * Real.log D / lambda)).trans
      ((le_max_right 1
        (max (1 / delta ^ 2) (2 * Real.log D / lambda))).trans hthreshold)
  have hn_const : 2 * Real.log D / lambda ≤ (n : ℝ) := by
    exact (le_max_right (1 / delta ^ 2) (2 * Real.log D / lambda)).trans
      ((le_max_right 1
        (max (1 / delta ^ 2) (2 * Real.log D / lambda))).trans hthreshold)
  have hsqrt := sqrt_natCast_le_mul_of_inv_sq_le hdelta hn_delta
  have hconstant : Real.log D ≤ (lambda / 2) * n := by
    have hmul := (div_le_iff₀ hlambda).mp hn_const
    nlinarith
  have hcoef : 2 * (d : ℝ) * delta ≤ lambda / 2 := by
    have hden : 0 < 4 * ((d : ℝ) + 1) := by positivity
    dsimp [delta]
    rw [show 2 * (d : ℝ) *
        (lambda / (4 * ((d : ℝ) + 1))) =
      (2 * (d : ℝ) * lambda) /
        (4 * ((d : ℝ) + 1)) by ring]
    apply (div_le_iff₀ hden).2
    have hd0 : (0 : ℝ) ≤ d := Nat.cast_nonneg d
    nlinarith
  have hsecond :
      2 * (d : ℝ) * Real.sqrt (n : ℝ) ≤
        (lambda / 2) * n := by
    calc
      2 * (d : ℝ) * Real.sqrt (n : ℝ) ≤
          2 * (d : ℝ) * (delta * n) := by
        exact mul_le_mul_of_nonneg_left hsqrt
          (mul_nonneg (by norm_num) (Nat.cast_nonneg d))
      _ = (2 * (d : ℝ) * delta) * n := by ring
      _ ≤ (lambda / 2) * n :=
        mul_le_mul_of_nonneg_right hcoef (Nat.cast_nonneg n)
  have hpolylog := packingLog_polynomial_natCast_le hC0 d hn_one
  have hlog : packingLog C ≤ lambda * n := by
    calc
      packingLog C ≤ packingLog (C0 * (n : ℝ) ^ d) :=
        packingLog_mono hC0' hcolumn
      _ ≤ Real.log D + 2 * (d : ℝ) * Real.sqrt (n : ℝ) := by
        simpa [D] using hpolylog
      _ ≤ (lambda / 2) * n + (lambda / 2) * n :=
        add_le_add hconstant hsecond
      _ = lambda * n := by ring
  have hdev := packingDeviation_le_of_linear_row_and_log
    hR0 hC0' hA hlambda.le hrow hlog
  have hlambda_sq : lambda ≤ epsilon ^ 2 / (1024 * Abar) :=
    min_le_left _ _
  have hlambda_lin : lambda ≤ epsilon / 16 := min_le_right _ _
  have hA_le : A ≤ Abar := by dsimp [Abar]; linarith
  have hAlambda : A * lambda ≤ epsilon ^ 2 / 1024 := by
    calc
      A * lambda ≤ Abar * lambda :=
        mul_le_mul_of_nonneg_right hA_le hlambda.le
      _ ≤ Abar * (epsilon ^ 2 / (1024 * Abar)) :=
        mul_le_mul_of_nonneg_left hlambda_sq hAbar.le
      _ = epsilon ^ 2 / 1024 := by field_simp
  have hsqrt_bound : Real.sqrt (A * lambda) ≤ epsilon / 32 := by
    have h0 : 0 ≤ A * lambda := mul_nonneg hA hlambda.le
    have he0 : 0 ≤ epsilon / 32 := by positivity
    have hsquare : (epsilon / 32) ^ 2 = epsilon ^ 2 / 1024 := by ring
    rw [← hsquare] at hAlambda
    exact Real.sqrt_le_iff.mpr ⟨he0, hAlambda⟩
  have hcoefFinal :
      4 * Real.sqrt (A * lambda) + 4 * lambda ≤ epsilon := by
    nlinarith
  exact hdev.trans
    (mul_le_mul_of_nonneg_right hcoefFinal (Nat.cast_nonneg n))

/-- Convenient degree-two specialization used by the current concrete
profile capacity column bound. -/
theorem packingDeviation_sublinear_of_linear_row_quadratic_column
    {A C0 : ℝ} (hA : 0 ≤ A) (hC0 : 0 ≤ C0) :
    ∀ epsilon : ℝ, 0 < epsilon → ∃ N : ℕ, ∀ n : ℕ, N ≤ n →
      ∀ R C : ℝ, 0 ≤ R → 0 ≤ C →
        R ≤ A * n → C ≤ C0 * (n : ℝ) ^ 2 →
          packingDeviation R C ≤ epsilon * n :=
  packingDeviation_sublinear_of_linear_row_polynomial_column hA hC0 2

end

end WeightedEdgeColoring.FinitePartialResamplingNumerics
