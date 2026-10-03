import WeightedEdgeColoring.RankThreeOriginalTypeNaturalIteration
import WeightedEdgeColoring.RankThreeResidualHarrisExponential

/-!
# Elementary bounds for the rounded natural job recurrence
-/

namespace WeightedEdgeColoring
namespace RankThreeOptionSystem.OriginalIterationState

/-- A rounded multiplicative recurrence with factor at most one never
exceeds its initial value. -/
theorem naturalSharpJobScale_le_initial
    (d0 n : ℕ) (a gamma eta : ℝ)
    (hr0 : 0 ≤ fixedSlackJobRetention a gamma - eta)
    (hr1 : fixedSlackJobRetention a gamma - eta ≤ 1) :
    naturalSharpJobScale d0 a gamma eta n ≤ d0 := by
  induction n with
  | zero => simp
  | succ n ih =>
      rw [naturalSharpJobScale_succ]
      let r := fixedSlackJobRetention a gamma - eta
      have harg : 0 ≤ r * naturalSharpJobScale d0 a gamma eta n :=
        mul_nonneg hr0 (by positivity)
      have hfloor :
          ((⌊r * naturalSharpJobScale d0 a gamma eta n⌋₊ : ℕ) : ℝ) ≤
            r * naturalSharpJobScale d0 a gamma eta n := Nat.floor_le harg
      have hstep : r * (naturalSharpJobScale d0 a gamma eta n : ℝ) ≤
          naturalSharpJobScale d0 a gamma eta n := by
        nlinarith
      have hreal :
          ((⌊r * naturalSharpJobScale d0 a gamma eta n⌋₊ : ℕ) : ℝ) ≤
            d0 := hfloor.trans (hstep.trans (by exact_mod_cast ih))
      exact_mod_cast hreal

/-- The total floor loss is at most one per round.  This affine lower bound
is useful when the number of rounds grows with the codegree. -/
theorem naturalSharpJobScale_affine_lower
    (d0 n : ℕ) (a gamma eta : ℝ)
    (hr0 : 0 ≤ fixedSlackJobRetention a gamma - eta)
    (hr1 : fixedSlackJobRetention a gamma - eta ≤ 1) :
    (d0 : ℝ) - n *
        ((1 - (fixedSlackJobRetention a gamma - eta)) * d0 + 1) ≤
      naturalSharpJobScale d0 a gamma eta n := by
  let r := fixedSlackJobRetention a gamma - eta
  have hrange : 0 ≤ 1 - r := sub_nonneg.mpr hr1
  have hupper : ∀ t, naturalSharpJobScale d0 a gamma eta t ≤ d0 :=
    fun t ↦ naturalSharpJobScale_le_initial d0 t a gamma eta hr0 hr1
  induction n with
  | zero => simp
  | succ n ih =>
      rw [naturalSharpJobScale_succ]
      have harg : 0 ≤ r * naturalSharpJobScale d0 a gamma eta n :=
        mul_nonneg hr0 (by positivity)
      have hfloor :
          r * (naturalSharpJobScale d0 a gamma eta n : ℝ) - 1 <
            (⌊r * naturalSharpJobScale d0 a gamma eta n⌋₊ : ℕ) := by
        have h := Nat.lt_floor_add_one
          (r * (naturalSharpJobScale d0 a gamma eta n : ℝ))
        nlinarith
      have hloss :
          (1 - r) * (naturalSharpJobScale d0 a gamma eta n : ℝ) ≤
            (1 - r) * d0 := by
        exact mul_le_mul_of_nonneg_left (by exact_mod_cast hupper n) hrange
      push_cast at ih ⊢
      dsimp [r] at ih hfloor hloss ⊢
      nlinarith

/-- A convenient half-initial-scale corollary. -/
theorem half_initial_le_naturalSharpJobScale
    (d0 n : ℕ) (a gamma eta : ℝ)
    (hr0 : 0 ≤ fixedSlackJobRetention a gamma - eta)
    (hr1 : fixedSlackJobRetention a gamma - eta ≤ 1)
    (hbudget : (n : ℝ) *
        ((1 - (fixedSlackJobRetention a gamma - eta)) * d0 + 1) ≤
      (d0 : ℝ) / 2) :
    (d0 : ℝ) / 2 ≤ naturalSharpJobScale d0 a gamma eta n := by
  have h := naturalSharpJobScale_affine_lower d0 n a gamma eta hr0 hr1
  nlinarith

/-- Keeping the multiplicative decay is essential when the number of
rounds is proportional to the codegree.  The accumulated floor error is at
most one per round. -/
theorem naturalSharpJobScale_pow_lower
    (d0 n : ℕ) (a gamma eta : ℝ)
    (hr0 : 0 ≤ fixedSlackJobRetention a gamma - eta)
    (hr1 : fixedSlackJobRetention a gamma - eta ≤ 1) :
    (fixedSlackJobRetention a gamma - eta) ^ n * d0 - n ≤
      naturalSharpJobScale d0 a gamma eta n := by
  let r := fixedSlackJobRetention a gamma - eta
  induction n with
  | zero => simp
  | succ n ih =>
      rw [naturalSharpJobScale_succ]
      have harg : 0 ≤ r * naturalSharpJobScale d0 a gamma eta n :=
        mul_nonneg hr0 (by positivity)
      have hfloor :
          r * (naturalSharpJobScale d0 a gamma eta n : ℝ) - 1 <
            (⌊r * naturalSharpJobScale d0 a gamma eta n⌋₊ : ℕ) := by
        have h := Nat.lt_floor_add_one
          (r * (naturalSharpJobScale d0 a gamma eta n : ℝ))
        nlinarith
      have hmul := mul_le_mul_of_nonneg_left ih hr0
      have hrn : r * (n : ℝ) ≤ n := by
        have hn0 : (0 : ℝ) ≤ n := by positivity
        nlinarith
      push_cast at ih hmul hfloor ⊢
      dsimp [r] at ih hmul hrn hfloor ⊢
      rw [pow_succ]
      nlinarith

/-- Exponential form of `naturalSharpJobScale_pow_lower`.  It loses only
an additive one per round and therefore remains useful for
`O(lambda)` rounds when the initial degree is much larger than `lambda`. -/
theorem naturalSharpJobScale_exp_lower
    (d0 n : ℕ) (a gamma eta : ℝ)
    (hr0 : 0 ≤ fixedSlackJobRetention a gamma - eta)
    (hrhalf : 1 / 2 ≤ fixedSlackJobRetention a gamma - eta)
    (hr1 : fixedSlackJobRetention a gamma - eta ≤ 1) :
    Real.exp
          (-2 * (1 - (fixedSlackJobRetention a gamma - eta)) * (n : ℝ)) * d0 - n ≤
      naturalSharpJobScale d0 a gamma eta n := by
  let r := fixedSlackJobRetention a gamma - eta
  let x := 1 - r
  have hx0 : 0 ≤ x := by dsimp [x, r]; linarith
  have hxhalf : x ≤ 1 / 2 := by dsimp [x, r]; linarith
  have hpow : Real.exp (-2 * x * (n : ℝ)) ≤ r ^ n := by
    simpa [x] using WeightedEdgeColoring.exp_neg_two_mul_nat_le_one_sub_pow x n hx0 hxhalf
  have hscale := naturalSharpJobScale_pow_lower d0 n a gamma eta hr0 hr1
  have hd0 : (0 : ℝ) ≤ d0 := by positivity
  have hmul := mul_le_mul_of_nonneg_right hpow hd0
  dsimp [x, r] at hmul ⊢
  nlinarith

/-- If the total real decay exponent is bounded by `C`, the current job
degree keeps the fixed fraction `exp(-2C)` of its initial value, apart from
the one-unit floor losses. -/
theorem naturalSharpJobScale_exp_budget_lower
    (d0 n : ℕ) (a gamma eta C : ℝ)
    (hr0 : 0 ≤ fixedSlackJobRetention a gamma - eta)
    (hrhalf : 1 / 2 ≤ fixedSlackJobRetention a gamma - eta)
    (hr1 : fixedSlackJobRetention a gamma - eta ≤ 1)
    (hbudget : (1 - (fixedSlackJobRetention a gamma - eta)) * n ≤ C) :
    Real.exp (-2 * C) * d0 - n ≤
      naturalSharpJobScale d0 a gamma eta n := by
  have hexp : Real.exp (-2 * C) ≤
      Real.exp
        (-2 * (1 - (fixedSlackJobRetention a gamma - eta)) * (n : ℝ)) := by
    apply Real.exp_le_exp.mpr
    nlinarith
  have hd0 : (0 : ℝ) ≤ d0 := by positivity
  have hmul := mul_le_mul_of_nonneg_right hexp hd0
  have hscale := naturalSharpJobScale_exp_lower d0 n a gamma eta
    hr0 hrhalf hr1
  nlinarith

/-- Uniform fixed-fraction lower bound through a prescribed number of
rounds.  The first premise controls the genuine multiplicative decay; the
second says that the additive floor losses are negligible on the initial
degree scale. -/
theorem naturalSharpJobScale_uniform_fraction
    (d0 N steps : ℕ) (a gamma eta c0 C : ℝ)
    (hr0 : 0 ≤ fixedSlackJobRetention a gamma - eta)
    (hrhalf : 1 / 2 ≤ fixedSlackJobRetention a gamma - eta)
    (hr1 : fixedSlackJobRetention a gamma - eta ≤ 1)
    (hc0 : 0 ≤ c0)
    (hd0 : c0 * N ≤ d0)
    (hdecay : (1 - (fixedSlackJobRetention a gamma - eta)) * steps ≤ C)
    (hfloor : (steps : ℝ) ≤ Real.exp (-2 * C) * c0 * N / 2) :
    ∀ n ≤ steps,
      (Real.exp (-2 * C) * c0 / 2) * N ≤
        naturalSharpJobScale d0 a gamma eta n := by
  intro n hn
  have hdecay0 : 0 ≤
      1 - (fixedSlackJobRetention a gamma - eta) := sub_nonneg.mpr hr1
  have hnR : (n : ℝ) ≤ steps := by exact_mod_cast hn
  have hbudget :
      (1 - (fixedSlackJobRetention a gamma - eta)) * n ≤ C := by
    exact (mul_le_mul_of_nonneg_left hnR hdecay0).trans hdecay
  have hscale := naturalSharpJobScale_exp_budget_lower
    d0 n a gamma eta C hr0 hrhalf hr1 hbudget
  have hexp0 : 0 ≤ Real.exp (-2 * C) := (Real.exp_pos _).le
  have hstart := mul_le_mul_of_nonneg_left hd0 hexp0
  have hnFloor : (n : ℝ) ≤ Real.exp (-2 * C) * c0 * N / 2 :=
    hnR.trans hfloor
  nlinarith

end RankThreeOptionSystem.OriginalIterationState
end WeightedEdgeColoring
