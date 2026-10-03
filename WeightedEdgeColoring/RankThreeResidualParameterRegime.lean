import Mathlib.Algebra.Order.Ring.Pow
import Mathlib.Analysis.SpecialFunctions.Exp

/-!
# Scalar parameters for the adaptive active-slot round

This file contains only real inequalities.  They record a parameter choice
for the active-slot residual round without making a graph-theoretic claim.

Write `x` for the current slot-degree bound divided by the fixed job-degree
scale and `ell` for the codegree scale.  With separate job and slot support
bounds one may use the fixed activity `a = kappa / ell`.  After the common
factor `x * N / ell^2` is removed, a convenient coarse bound gives lower and
upper dependency coefficients `96 * kappa^2` and `56 * kappa^2`.  Thus a
sufficiently small absolute `kappa` leaves a positive exponential margin.

The lemmas with constants 168 and 108 are retained as a fallback for the
older common-ambient support bounds.  They also support the adaptive choice
`a = kappa * x / ell`.

The final lemmas record the useful deterministic recurrence.  If the slot
ratio falls by `a*x/40` and a surviving job loses at most `8*a*x`, then the
total job loss is at most 320 times the total fall in the slot ratio.
-/

namespace WeightedEdgeColoring

/-- The concrete choice `kappa = 10^-6` satisfies the lower-row restriction. -/
theorem one_millionth_lower_parameter :
    168 * (1 / 1000000 : ℝ) ≤ 1 / 320 := by norm_num

/-- The same concrete choice satisfies the weaker upper-row restriction. -/
theorem one_millionth_upper_parameter :
    108 * (1 / 1000000 : ℝ) ≤ 1 := by norm_num

/-- Tight separate-scale lower rows pay coefficient 96 instead of 168. -/
theorem tight_lower_exponent_margin
    (kappa Z : ℝ) (hkappa0 : 0 ≤ kappa) (hZ0 : 0 ≤ Z)
    (hkappa : 96 * kappa ≤ 1 / 320) :
    96 * kappa ^ 2 * Z + kappa * Z / 320 ≤ kappa * Z / 160 := by
  have hmul : 96 * kappa ^ 2 ≤ kappa / 320 := by
    calc
      96 * kappa ^ 2 = kappa * (96 * kappa) := by ring
      _ ≤ kappa * (1 / 320) :=
        mul_le_mul_of_nonneg_left hkappa hkappa0
      _ = kappa / 320 := by ring
  have := mul_le_mul_of_nonneg_right hmul hZ0
  linarith

/-- Exponential form of the tight separate-scale lower margin. -/
theorem tight_lower_exp_le
    (kappa Z rowX : ℝ) (hkappa0 : 0 ≤ kappa) (hZ0 : 0 ≤ Z)
    (hkappa : 96 * kappa ≤ 1 / 320)
    (hscale : Real.exp (-(kappa * Z / 320)) ≤ rowX) :
    Real.exp (-(kappa * Z / 160)) ≤
      rowX * Real.exp (-(96 * kappa ^ 2 * Z)) := by
  have hmargin := tight_lower_exponent_margin
    kappa Z hkappa0 hZ0 hkappa
  have hexp : Real.exp (-(kappa * Z / 160)) ≤
      Real.exp (-(96 * kappa ^ 2 * Z) - kappa * Z / 320) := by
    apply Real.exp_le_exp.mpr
    linarith
  calc
    Real.exp (-(kappa * Z / 160)) ≤
        Real.exp (-(96 * kappa ^ 2 * Z) - kappa * Z / 320) := hexp
    _ = Real.exp (-(96 * kappa ^ 2 * Z)) *
        Real.exp (-(kappa * Z / 320)) := by
      rw [show -(96 * kappa ^ 2 * Z) - kappa * Z / 320 =
        -(96 * kappa ^ 2 * Z) + -(kappa * Z / 320) by ring,
        Real.exp_add]
    _ ≤ Real.exp (-(96 * kappa ^ 2 * Z)) * rowX :=
      mul_le_mul_of_nonneg_left hscale (Real.exp_nonneg _)
    _ = rowX * Real.exp (-(96 * kappa ^ 2 * Z)) := by ring

/-- Tight separate-scale upper rows pay coefficient 56. -/
theorem tight_upper_exponent_margin
    (kappa Z : ℝ) (hkappa0 : 0 ≤ kappa) (hZ0 : 0 ≤ Z)
    (hkappa : 56 * kappa ≤ 1) :
    56 * kappa ^ 2 * Z + kappa * Z ≤ 2 * kappa * Z := by
  have hmul : 56 * kappa ^ 2 ≤ kappa := by
    calc
      56 * kappa ^ 2 = kappa * (56 * kappa) := by ring
      _ ≤ kappa * 1 := mul_le_mul_of_nonneg_left hkappa hkappa0
      _ = kappa := by ring
  have := mul_le_mul_of_nonneg_right hmul hZ0
  linarith

/-- Exponential form of the tight separate-scale upper margin. -/
theorem tight_upper_exp_le
    (kappa Z rowX : ℝ) (hkappa0 : 0 ≤ kappa) (hZ0 : 0 ≤ Z)
    (hkappa : 56 * kappa ≤ 1)
    (hscale : Real.exp (-(kappa * Z)) ≤ rowX) :
    Real.exp (-(2 * kappa * Z)) ≤
      rowX * Real.exp (-(56 * kappa ^ 2 * Z)) := by
  have hmargin := tight_upper_exponent_margin
    kappa Z hkappa0 hZ0 hkappa
  have hexp : Real.exp (-(2 * kappa * Z)) ≤
      Real.exp (-(56 * kappa ^ 2 * Z) - kappa * Z) := by
    apply Real.exp_le_exp.mpr
    linarith
  calc
    Real.exp (-(2 * kappa * Z)) ≤
        Real.exp (-(56 * kappa ^ 2 * Z) - kappa * Z) := hexp
    _ = Real.exp (-(56 * kappa ^ 2 * Z)) *
        Real.exp (-(kappa * Z)) := by
      rw [show -(56 * kappa ^ 2 * Z) - kappa * Z =
        -(56 * kappa ^ 2 * Z) + -(kappa * Z) by ring,
        Real.exp_add]
    _ ≤ Real.exp (-(56 * kappa ^ 2 * Z)) * rowX :=
      mul_le_mul_of_nonneg_left hscale (Real.exp_nonneg _)
    _ = rowX * Real.exp (-(56 * kappa ^ 2 * Z)) := by ring

/-- The lower-tail exponent pays the dependency exponent and still leaves
`kappa * Z / 320` of exponential margin. -/
theorem adaptive_lower_exponent_margin
    (kappa Z : ℝ) (hkappa0 : 0 ≤ kappa) (hZ0 : 0 ≤ Z)
    (hkappa : 168 * kappa ≤ 1 / 320) :
    168 * kappa ^ 2 * Z + kappa * Z / 320 ≤ kappa * Z / 160 := by
  have hmul : 168 * kappa ^ 2 ≤ kappa / 320 := by
    calc
      168 * kappa ^ 2 = kappa * (168 * kappa) := by ring
      _ ≤ kappa * (1 / 320) :=
        mul_le_mul_of_nonneg_left hkappa hkappa0
      _ = kappa / 320 := by ring
  have := mul_le_mul_of_nonneg_right hmul hZ0
  linarith

/-- Exponential form of `adaptive_lower_exponent_margin`.  This is the
shape used by the lower rows of the Harris local lemma. -/
theorem adaptive_lower_exp_le
    (kappa Z rowX : ℝ) (hkappa0 : 0 ≤ kappa) (hZ0 : 0 ≤ Z)
    (hkappa : 168 * kappa ≤ 1 / 320)
    (hscale : Real.exp (-(kappa * Z / 320)) ≤ rowX) :
    Real.exp (-(kappa * Z / 160)) ≤
      rowX * Real.exp (-(168 * kappa ^ 2 * Z)) := by
  have hmargin := adaptive_lower_exponent_margin
    kappa Z hkappa0 hZ0 hkappa
  have hexp : Real.exp (-(kappa * Z / 160)) ≤
      Real.exp (-(168 * kappa ^ 2 * Z) - kappa * Z / 320) := by
    apply Real.exp_le_exp.mpr
    linarith
  calc
    Real.exp (-(kappa * Z / 160)) ≤
        Real.exp (-(168 * kappa ^ 2 * Z) - kappa * Z / 320) := hexp
    _ = Real.exp (-(168 * kappa ^ 2 * Z)) *
        Real.exp (-(kappa * Z / 320)) := by
      rw [show -(168 * kappa ^ 2 * Z) - kappa * Z / 320 =
        -(168 * kappa ^ 2 * Z) + -(kappa * Z / 320) by ring,
        Real.exp_add]
    _ ≤ Real.exp (-(168 * kappa ^ 2 * Z)) * rowX :=
      mul_le_mul_of_nonneg_left hscale (Real.exp_nonneg _)
    _ = rowX * Real.exp (-(168 * kappa ^ 2 * Z)) := by ring

/-- The upper job tail leaves `kappa * Z` of margin after paying the upper
row dependency exponent. -/
theorem adaptive_upper_exponent_margin
    (kappa Z : ℝ) (hkappa0 : 0 ≤ kappa) (hZ0 : 0 ≤ Z)
    (hkappa : 108 * kappa ≤ 1) :
    108 * kappa ^ 2 * Z + kappa * Z ≤ 2 * kappa * Z := by
  have hmul : 108 * kappa ^ 2 ≤ kappa := by
    calc
      108 * kappa ^ 2 = kappa * (108 * kappa) := by ring
      _ ≤ kappa * 1 := mul_le_mul_of_nonneg_left hkappa hkappa0
      _ = kappa := by ring
  have := mul_le_mul_of_nonneg_right hmul hZ0
  linarith

/-- Exponential form of `adaptive_upper_exponent_margin`. -/
theorem adaptive_upper_exp_le
    (kappa Z rowX : ℝ) (hkappa0 : 0 ≤ kappa) (hZ0 : 0 ≤ Z)
    (hkappa : 108 * kappa ≤ 1)
    (hscale : Real.exp (-(kappa * Z)) ≤ rowX) :
    Real.exp (-(2 * kappa * Z)) ≤
      rowX * Real.exp (-(108 * kappa ^ 2 * Z)) := by
  have hmargin := adaptive_upper_exponent_margin
    kappa Z hkappa0 hZ0 hkappa
  have hexp : Real.exp (-(2 * kappa * Z)) ≤
      Real.exp (-(108 * kappa ^ 2 * Z) - kappa * Z) := by
    apply Real.exp_le_exp.mpr
    linarith
  calc
    Real.exp (-(2 * kappa * Z)) ≤
        Real.exp (-(108 * kappa ^ 2 * Z) - kappa * Z) := hexp
    _ = Real.exp (-(108 * kappa ^ 2 * Z)) *
        Real.exp (-(kappa * Z)) := by
      rw [show -(108 * kappa ^ 2 * Z) - kappa * Z =
        -(108 * kappa ^ 2 * Z) + -(kappa * Z) by ring,
        Real.exp_add]
    _ ≤ Real.exp (-(108 * kappa ^ 2 * Z)) * rowX :=
      mul_le_mul_of_nonneg_left hscale (Real.exp_nonneg _)
    _ = rowX * Real.exp (-(108 * kappa ^ 2 * Z)) := by ring

/-- Doubling the pair-event local-lemma weight pays any exponential neighbor
product whose exponent is at most one half. -/
theorem doubled_pair_weight_pays_small_exponent
    (rho t : ℝ) (ht : t ≤ 1 / 2) :
    rho ^ 2 ≤ (2 * rho ^ 2) * Real.exp (-t) := by
  have hexp : 1 / 2 ≤ Real.exp (-t) := by
    have hbase := Real.add_one_le_exp (-t)
    linarith
  nlinarith [sq_nonneg rho, Real.exp_pos (-t)]

/-- One recurrence step preserves the affine invariant
`d >= d0 - 320 * (x0 - x)`. -/
theorem adaptive_degree_invariant_step
    (d0 x0 d x d' x' a : ℝ)
    (hinv : d0 - 320 * (x0 - x) ≤ d)
    (hx : x' = x - a * x / 40)
    (hd : d - 8 * a * x ≤ d') :
    d0 - 320 * (x0 - x') ≤ d' := by
  rw [hx]
  linarith

/-- Iterated form of `adaptive_degree_invariant_step`. -/
theorem adaptive_degree_invariant
    (d x a : ℕ → ℝ)
    (hx : ∀ t, x (t + 1) = x t - a t * x t / 40)
    (hd : ∀ t, d t - 8 * a t * x t ≤ d (t + 1)) :
    ∀ n, d 0 - 320 * (x 0 - x n) ≤ d n := by
  intro n
  induction n with
  | zero => simp
  | succ n ih =>
      exact adaptive_degree_invariant_step
        (d 0) (x 0) (d n) (x n) (d (n + 1)) (x (n + 1)) (a n)
          ih (hx n) (hd n)

/-- If the initial slot ratio is at most `1/640`, the affine invariant and
nonnegativity of the current slot ratio keep every surviving job degree at
least half of its initial scale. -/
theorem adaptive_degree_half_of_slot_slack
    (d x x0 : ℝ) (hx : 0 ≤ x) (hx0 : x0 ≤ 1 / 640)
    (hinv : 1 - 320 * (x0 - x) ≤ d) :
    1 / 2 ≤ d := by
  linarith

/-- One coverage step by a fraction `a/8` is at least as strong as the fifth
power of a slot step by `a/40`. -/
theorem adaptive_coverage_factor_le_slot_factor_pow_five
    (a : ℝ) (ha : a ≤ 80) :
    1 - a / 8 ≤ (1 - a / 40) ^ 5 := by
  have h := one_add_mul_le_pow (a := -(a / 40)) (n := 5) (by linarith)
  calc
    1 - a / 8 = 1 + (5 : ℝ) * (-(a / 40)) := by ring
    _ ≤ (1 + (-(a / 40))) ^ 5 := h
    _ = (1 - a / 40) ^ 5 := by ring

end WeightedEdgeColoring
