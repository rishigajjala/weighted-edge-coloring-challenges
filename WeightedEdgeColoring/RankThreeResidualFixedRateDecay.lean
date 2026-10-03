import WeightedEdgeColoring.RankThreeResidualFixedRateRecurrence
import WeightedEdgeColoring.RankThreeResidualFixedRateCoverage

/-!
# Comparing slot decay with covered-weight decay

The slot cap cannot fall faster than the ideal multiplicative factor
`1-kappa/(40*lambda)`.  The square of the retained-weight factor
`1-kappa/(64*lambda)` is at most that slot factor.  Consequently, whenever
the slot cap has fallen to an `epsilon^2` fraction of its initial value, the
geometric uncovered-weight factor is already at most `epsilon`.
-/

namespace WeightedEdgeColoring

noncomputable def fixedRateSlotRetention (lambda : ℕ) : ℝ :=
  1 - fixedRateKappa / (40 * (lambda : ℝ))

noncomputable def fixedRateCoverageRetention (lambda : ℕ) : ℝ :=
  1 - fixedRateCoverageRate lambda

theorem fixedRateSlotRetention_nonneg
    (lambda : ℕ) (hlambda : 0 < lambda) :
    0 ≤ fixedRateSlotRetention lambda := by
  have hlambdaR : (1 : ℝ) ≤ (lambda : ℝ) := by exact_mod_cast hlambda
  rw [fixedRateSlotRetention]
  have : fixedRateKappa / (40 * (lambda : ℝ)) ≤ 1 := by
    rw [div_le_one (by positivity : (0 : ℝ) < 40 * (lambda : ℝ))]
    norm_num [fixedRateKappa]
    linarith
  linarith

theorem fixedRateSlotRetention_le_one (lambda : ℕ) :
    fixedRateSlotRetention lambda ≤ 1 := by
  rw [fixedRateSlotRetention]
  exact sub_le_self 1 (div_nonneg fixedRateKappa_nonneg
    (mul_nonneg (by norm_num) (Nat.cast_nonneg lambda)))

theorem fixedRateCoverageRetention_nonneg
    (lambda : ℕ) (hlambda : 0 < lambda) :
    0 ≤ fixedRateCoverageRetention lambda := by
  rw [fixedRateCoverageRetention]
  exact sub_nonneg.mpr (fixedRateCoverageRate_le_one lambda hlambda)

theorem fixedRateCoverageRetention_le_one (lambda : ℕ) :
    fixedRateCoverageRetention lambda ≤ 1 := by
  rw [fixedRateCoverageRetention]
  exact sub_le_self 1 (fixedRateCoverageRate_nonneg lambda)

/-- The square of the retained-weight factor is bounded by the retained-slot
factor.  The very small fixed value of `kappa` leaves ample slack. -/
theorem fixedRateCoverageRetention_sq_le_slotRetention
    (lambda : ℕ) (hlambda : 0 < lambda) :
    fixedRateCoverageRetention lambda ^ 2 ≤
      fixedRateSlotRetention lambda := by
  let x : ℝ := fixedRateKappa / (lambda : ℝ)
  have hx0 : 0 ≤ x := by
    exact div_nonneg fixedRateKappa_nonneg (Nat.cast_nonneg lambda)
  have hx1 : x ≤ 1 := by
    have hlambdaR : (1 : ℝ) ≤ (lambda : ℝ) := by exact_mod_cast hlambda
    dsimp [x]
    rw [div_le_one (by positivity : (0 : ℝ) < (lambda : ℝ))]
    norm_num [fixedRateKappa]
    linarith
  have hidCoverage : fixedRateCoverageRetention lambda = 1 - x / 64 := by
    simp only [fixedRateCoverageRetention, fixedRateCoverageRate]
    dsimp [x]
    field_simp
  have hidSlot : fixedRateSlotRetention lambda = 1 - x / 40 := by
    simp only [fixedRateSlotRetention]
    dsimp [x]
    field_simp
  rw [hidCoverage, hidSlot]
  nlinarith [sq_nonneg x]

/-- One rounded slot update retains at least the ideal slot factor. -/
theorem fixedRateSlotRetention_mul_le_next
    (lambda S : ℕ) (hlambda : 0 < lambda) :
    fixedRateSlotRetention lambda * (S : ℝ) ≤
      (fixedRateNextSlotBound lambda S : ℝ) := by
  have hbudget := fixedRateSlotBudget_cast_le lambda S
  have hhalf : ((fixedRateSlotBudget lambda S / 2 : ℕ) : ℝ) ≤
      (fixedRateKappa * (S : ℝ) / (20 * (lambda : ℝ))) / 2 := by
    calc
      ((fixedRateSlotBudget lambda S / 2 : ℕ) : ℝ) ≤
          (fixedRateSlotBudget lambda S : ℝ) / 2 := by
        have hnat : 2 * (fixedRateSlotBudget lambda S / 2) ≤
            fixedRateSlotBudget lambda S := Nat.mul_div_le _ _
        have hreal : (2 : ℝ) * (fixedRateSlotBudget lambda S / 2 : ℕ) ≤
            (fixedRateSlotBudget lambda S : ℝ) := by
          exact_mod_cast hnat
        linarith
      _ ≤ (fixedRateKappa * (S : ℝ) / (20 * (lambda : ℝ))) / 2 :=
        div_le_div_of_nonneg_right hbudget (by norm_num)
  have hb := fixedRateSlotBudget_le_slotBound lambda S hlambda
  have hq : fixedRateSlotBudget lambda S / 2 ≤ S :=
    (Nat.div_le_self _ _).trans hb
  rw [fixedRateNextSlotBound, Nat.cast_sub hq, fixedRateSlotRetention]
  have hlambdaR : (0 : ℝ) < (lambda : ℝ) := by positivity
  calc
    (1 - fixedRateKappa / (40 * (lambda : ℝ))) * (S : ℝ) =
        (S : ℝ) -
          (fixedRateKappa * (S : ℝ) / (20 * (lambda : ℝ))) / 2 := by
      field_simp
      ring
    _ ≤ (S : ℝ) - (fixedRateSlotBudget lambda S / 2 : ℕ) :=
      sub_le_sub_left hhalf _

/-- Iterated lower bound on the rounded slot cap. -/
theorem fixedRateSlotRetention_pow_mul_le_slotCap
    (lambda S0 n : ℕ) (hlambda : 0 < lambda) :
    fixedRateSlotRetention lambda ^ n * (S0 : ℝ) ≤
      (fixedRateSlotCap lambda S0 n : ℝ) := by
  induction n with
  | zero => simp
  | succ n ih =>
      rw [fixedRateSlotCap_succ, pow_succ]
      have hfactor := fixedRateSlotRetention_nonneg lambda hlambda
      calc
        (fixedRateSlotRetention lambda ^ n * fixedRateSlotRetention lambda) *
              (S0 : ℝ) =
            fixedRateSlotRetention lambda *
              (fixedRateSlotRetention lambda ^ n * (S0 : ℝ)) := by ring
        _ ≤ fixedRateSlotRetention lambda *
              (fixedRateSlotCap lambda S0 n : ℝ) :=
          mul_le_mul_of_nonneg_left ih hfactor
        _ ≤ (fixedRateNextSlotBound lambda
              (fixedRateSlotCap lambda S0 n) : ℝ) :=
          fixedRateSlotRetention_mul_le_next lambda _ hlambda

/-- Power form of the square comparison. -/
theorem fixedRateCoverageRetention_pow_two_le_slot_pow
    (lambda n : ℕ) (hlambda : 0 < lambda) :
    fixedRateCoverageRetention lambda ^ (2 * n) ≤
      fixedRateSlotRetention lambda ^ n := by
  calc
    fixedRateCoverageRetention lambda ^ (2 * n) =
        (fixedRateCoverageRetention lambda ^ 2) ^ n := by rw [pow_mul]
    _ ≤ fixedRateSlotRetention lambda ^ n :=
      pow_le_pow_left₀ (sq_nonneg (fixedRateCoverageRetention lambda))
        (fixedRateCoverageRetention_sq_le_slotRetention lambda hlambda) n

/-- Reaching an `epsilon^2` fraction of the initial slot cap forces the
geometric active-weight factor below `epsilon`. -/
theorem fixedRateCoverageRetention_pow_le_of_slotCap
    (lambda S0 n : ℕ) (epsilon : ℝ)
    (hlambda : 0 < lambda) (hS0 : 0 < S0) (hepsilon : 0 ≤ epsilon)
    (hcap : (fixedRateSlotCap lambda S0 n : ℝ) ≤
      epsilon ^ 2 * (S0 : ℝ)) :
    fixedRateCoverageRetention lambda ^ n ≤ epsilon := by
  have hslot := fixedRateSlotRetention_pow_mul_le_slotCap
    lambda S0 n hlambda
  have hS0R : (0 : ℝ) < (S0 : ℝ) := by positivity
  have hslotPow : fixedRateSlotRetention lambda ^ n ≤ epsilon ^ 2 := by
    have hmul := hslot.trans hcap
    nlinarith
  have hcovPow := (fixedRateCoverageRetention_pow_two_le_slot_pow
    lambda n hlambda).trans hslotPow
  have hnonneg : 0 ≤ fixedRateCoverageRetention lambda ^ n :=
    pow_nonneg (fixedRateCoverageRetention_nonneg lambda hlambda) n
  have hpow : fixedRateCoverageRetention lambda ^ (2 * n) =
      (fixedRateCoverageRetention lambda ^ n) ^ 2 := by
    rw [Nat.mul_comm, pow_mul]
  rw [hpow] at hcovPow
  nlinarith [sq_nonneg
    (fixedRateCoverageRetention lambda ^ n - epsilon)]

end WeightedEdgeColoring
