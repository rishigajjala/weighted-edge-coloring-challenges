import WeightedEdgeColoring.FinitePartialResamplingChargeBounds

/-!
# Final arithmetic for the lambda-form partial-resampling criterion

Once every row has self-charge at most one half, division by `1 - S` costs at
most a factor two.  The source-charge estimate `theta / 4` therefore fits
inside the available lambda slack `theta`, with a factor-two margin.
-/

namespace WeightedEdgeColoring.FinitePartialResamplingNumerics

open scoped BigOperators

variable {Row Source : Type*}
variable [Fintype Row]

theorem sum_charge_div_one_sub_le_twice
    (self : Row → ℝ) (charge : Row → ℝ)
    (hself : ∀ r, self r ≤ 1 / 2)
    (hcharge : ∀ r, 0 ≤ charge r) :
    (∑ r, charge r / (1 - self r)) ≤ 2 * ∑ r, charge r := by
  calc
    (∑ r, charge r / (1 - self r)) ≤ ∑ r, 2 * charge r := by
      apply Finset.sum_le_sum
      intro r _hr
      have hden : 1 / 2 ≤ 1 - self r := by linarith [hself r]
      calc
        charge r / (1 - self r) ≤ charge r / (1 / 2) := by
          exact div_le_div_of_nonneg_left (hcharge r) (by norm_num) hden
        _ = 2 * charge r := by ring
    _ = 2 * ∑ r, charge r := by rw [Finset.mul_sum]

/-- The concrete one-half and quarter-theta estimates imply the numerical
hypothesis of the Harris--Srinivasan lambda criterion. -/
theorem packing_lambda_criterion_arithmetic
    {R C : ℝ} (hR : 0 < R) (hC : 0 ≤ C)
    (self : Row → ℝ) (charge : Row → Source → ℝ)
    (hself : ∀ r, self r ≤ 1 / 2)
    (hcharge : ∀ r i, 0 ≤ charge r i)
    (hsum : ∀ i, ∑ r, charge r i ≤ packingTheta R C / 4) :
    ∀ i,
      1 + ∑ r, charge r i / (1 - self r) ≤
        1 + packingTheta R C := by
  intro i
  have htwice := sum_charge_div_one_sub_le_twice self (fun r ↦ charge r i)
    hself (fun r ↦ hcharge r i)
  have htheta0 := packingTheta_nonneg hR hC
  have hbound : (∑ r, charge r i / (1 - self r)) ≤ packingTheta R C := by
    calc
      (∑ r, charge r i / (1 - self r)) ≤
          2 * ∑ r, charge r i := htwice
      _ ≤ 2 * (packingTheta R C / 4) :=
        mul_le_mul_of_nonneg_left (hsum i) (by norm_num)
      _ ≤ packingTheta R C := by nlinarith
  linarith

end WeightedEdgeColoring.FinitePartialResamplingNumerics
