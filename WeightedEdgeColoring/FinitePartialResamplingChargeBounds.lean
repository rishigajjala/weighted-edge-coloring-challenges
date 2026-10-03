import WeightedEdgeColoring.FinitePartialResamplingNumericsBounds
import WeightedEdgeColoring.FinitePartialResamplingCapped

/-!
# Charge estimates at the chosen partial-resampling parameters

The exponential module bounds charges in terms of a row mean.  The numerical
module chooses the parameter and threshold.  This file joins those two facts.
It proves, for arbitrary finite categorical data, that every row has
self-charge at most one half and that the sum of source charges through one
column is at most `theta / 8`.

No partial-resampling existence theorem is used here.  These are the exact
finite inequalities that such a theorem will consume.
-/

namespace WeightedEdgeColoring.FinitePartialResamplingNumerics

open scoped BigOperators
open WeightedEdgeColoring.FinitePartialResamplingExponential

variable {Source State Row : Type*}
variable [Fintype Source] [DecidableEq Source]
variable [Fintype State] [DecidableEq State]

private theorem sourceMean_nonneg
    {a lambda : Source → State → ℝ}
    (hlambda : ∀ i j, 0 ≤ lambda i j)
    (ha0 : ∀ i j, 0 ≤ a i j) (i : Source) :
    0 ≤ sourceMean lambda a i := by
  unfold sourceMean
  exact Finset.sum_nonneg fun j _ ↦ mul_nonneg (hlambda i j) (ha0 i j)

/-- A row whose inflated mean is at most `(1 + theta) R` has self-charge at
most one half. -/
theorem expSelfCharge_packing_le_half
    {R C : ℝ} (hR : 0 < R) (hC : 0 ≤ C)
    {a lambda : Source → State → ℝ}
    (hlambda : ∀ i j, 0 ≤ lambda i j)
    (ha0 : ∀ i j, 0 ≤ a i j)
    (ha1 : ∀ i j, a i j ≤ 1)
    (hmean : weightedMean lambda a ≤ (1 + packingTheta R C) * R) :
    expSelfCharge (packingTheta R C) (packingThreshold R C) a lambda ≤
      1 / 2 := by
  have htheta := packingTheta_pos hR hC
  have hthreshold := packingThreshold_pos hR hC
  have hkernel0 : 0 ≤ Real.exp (packingTheta R C) - 1 :=
    sub_nonneg.mpr (Real.one_le_exp htheta.le)
  have hexponent :
      (Real.exp (packingTheta R C) - 1) * weightedMean lambda a ≤
        packingExponent R C := by
    have hscaled := mul_le_mul_of_nonneg_left hmean hkernel0
    calc
      (Real.exp (packingTheta R C) - 1) * weightedMean lambda a ≤
          (Real.exp (packingTheta R C) - 1) *
            ((1 + packingTheta R C) * R) := hscaled
      _ = packingExponent R C := by
        unfold packingExponent
        ring
  have hden0 := (packingDenominator_pos hR hC).le
  calc
    expSelfCharge (packingTheta R C) (packingThreshold R C) a lambda ≤
        Real.exp ((Real.exp (packingTheta R C) - 1) *
            weightedMean lambda a) /
          (Real.exp (packingTheta R C * packingThreshold R C) - 1) :=
      expSelfCharge_le htheta hthreshold hlambda ha0 ha1
    _ ≤ Real.exp (packingExponent R C) /
          (Real.exp (packingTheta R C * packingThreshold R C) - 1) := by
      exact div_le_div_of_nonneg_right
        (Real.exp_le_exp.mpr hexponent) hden0
    _ ≤ 1 / 2 := packingSelfFactor_le_half hR hC

/-- One row's source charge is linear in that source's physical mean, with
the common factor `2 theta / (2 + 16 C)`. -/
theorem expSourceCharge_packing_le
    {R C : ℝ} (hR : 0 < R) (hC : 0 ≤ C)
    {a lambda : Source → State → ℝ}
    (hlambda : ∀ i j, 0 ≤ lambda i j)
    (ha0 : ∀ i j, 0 ≤ a i j)
    (ha1 : ∀ i j, a i j ≤ 1)
    (hmean : weightedMean lambda a ≤ (1 + packingTheta R C) * R)
    (i : Source) :
    expSourceCharge (packingTheta R C) (packingThreshold R C) a lambda i ≤
      sourceMean lambda a i *
        (2 * packingTheta R C / (2 + 16 * C)) := by
  have htheta := packingTheta_pos hR hC
  have hthreshold := packingThreshold_pos hR hC
  have hkernel0 : 0 ≤ Real.exp (packingTheta R C) - 1 :=
    sub_nonneg.mpr (Real.one_le_exp htheta.le)
  have hsource0 := sourceMean_nonneg hlambda ha0 i
  have hexponent :
      (Real.exp (packingTheta R C) - 1) * weightedMean lambda a ≤
        packingExponent R C := by
    have hscaled := mul_le_mul_of_nonneg_left hmean hkernel0
    calc
      (Real.exp (packingTheta R C) - 1) * weightedMean lambda a ≤
          (Real.exp (packingTheta R C) - 1) *
            ((1 + packingTheta R C) * R) := hscaled
      _ = packingExponent R C := by
        unfold packingExponent
        ring
  have hexp :
      Real.exp ((Real.exp (packingTheta R C) - 1) * weightedMean lambda a) ≤
        Real.exp (packingExponent R C) :=
    Real.exp_le_exp.mpr hexponent
  have hden0 := (packingDenominator_pos hR hC).le
  have hmiddle :
      ((Real.exp (packingTheta R C) - 1) * sourceMean lambda a i) *
            Real.exp ((Real.exp (packingTheta R C) - 1) *
              weightedMean lambda a) /
          (Real.exp (packingTheta R C * packingThreshold R C) - 1) ≤
        sourceMean lambda a i *
          (((Real.exp (packingTheta R C) - 1) *
              Real.exp (packingExponent R C)) /
            (Real.exp (packingTheta R C * packingThreshold R C) - 1)) := by
    have hnum :
        ((Real.exp (packingTheta R C) - 1) * sourceMean lambda a i) *
            Real.exp ((Real.exp (packingTheta R C) - 1) *
              weightedMean lambda a) ≤
          ((Real.exp (packingTheta R C) - 1) * sourceMean lambda a i) *
            Real.exp (packingExponent R C) :=
      mul_le_mul_of_nonneg_left hexp (mul_nonneg hkernel0 hsource0)
    have hdiv := div_le_div_of_nonneg_right hnum hden0
    convert hdiv using 1 <;> ring
  calc
    expSourceCharge (packingTheta R C) (packingThreshold R C) a lambda i ≤
        (((Real.exp (packingTheta R C) - 1) * sourceMean lambda a i) *
          Real.exp ((Real.exp (packingTheta R C) - 1) *
            weightedMean lambda a)) /
          (Real.exp (packingTheta R C * packingThreshold R C) - 1) :=
      expSourceCharge_le i htheta hthreshold hlambda ha0 ha1
    _ ≤ sourceMean lambda a i *
          (((Real.exp (packingTheta R C) - 1) *
              Real.exp (packingExponent R C)) /
            (Real.exp (packingTheta R C * packingThreshold R C) - 1)) :=
      hmiddle
    _ ≤ sourceMean lambda a i *
          (2 * packingTheta R C / (2 + 16 * C)) :=
      mul_le_mul_of_nonneg_left (packingSourceFactor_le hR hC) hsource0

/-- If the total physical mean through one source, summed over all rows, is
at most `C`, then the total source charge is at most `theta / 8`. -/
theorem sum_expSourceCharge_packing_le
    [Fintype Row]
    {R C : ℝ} (hR : 0 < R) (hC : 0 ≤ C)
    (a : Row → Source → State → ℝ)
    (lambda : Source → State → ℝ)
    (hlambda : ∀ i j, 0 ≤ lambda i j)
    (ha0 : ∀ r i j, 0 ≤ a r i j)
    (ha1 : ∀ r i j, a r i j ≤ 1)
    (hmean : ∀ r,
      weightedMean lambda (a r) ≤ (1 + packingTheta R C) * R)
    (hcolumn : ∀ i, ∑ r, sourceMean lambda (a r) i ≤ C)
    (i : Source) :
    (∑ r, expSourceCharge (packingTheta R C) (packingThreshold R C)
      (a r) lambda i) ≤ packingTheta R C / 8 := by
  let factor := 2 * packingTheta R C / (2 + 16 * C)
  have hfactor0 : 0 ≤ factor := by
    dsimp [factor]
    exact div_nonneg
      (mul_nonneg (by norm_num) (packingTheta_nonneg hR hC)) (by linarith)
  calc
    (∑ r, expSourceCharge (packingTheta R C) (packingThreshold R C)
        (a r) lambda i) ≤
        ∑ r, sourceMean lambda (a r) i * factor := by
      exact Finset.sum_le_sum fun r _ ↦ by
        simpa [factor] using expSourceCharge_packing_le hR hC hlambda
          (ha0 r) (ha1 r) (hmean r) i
    _ = (∑ r, sourceMean lambda (a r) i) * factor := by
      rw [Finset.sum_mul]
    _ ≤ C * factor :=
      mul_le_mul_of_nonneg_right (hcolumn i) hfactor0
    _ = factor * C := by ring
    _ ≤ packingTheta R C / 8 := by
      simpa [factor] using packingSourceColumnFactor_le hR hC

/-- With an uninflated coefficient-column budget `C`, inflating a probability
law by at most two gives a source-mean budget `2 C`.  The available slack then
gives the still-sufficient bound `theta / 4`. -/
theorem packingSourceDoubleColumnFactor_le
    {R C : ℝ} (hR : 0 < R) (hC : 0 ≤ C) :
    (2 * packingTheta R C / (2 + 16 * C)) * (2 * C) ≤
      packingTheta R C / 4 := by
  calc
    (2 * packingTheta R C / (2 + 16 * C)) * (2 * C) =
        2 * ((2 * packingTheta R C / (2 + 16 * C)) * C) := by ring
    _ ≤ 2 * (packingTheta R C / 8) := by
      exact mul_le_mul_of_nonneg_left
        (packingSourceColumnFactor_le hR hC) (by norm_num)
    _ = packingTheta R C / 4 := by ring

theorem sum_expSourceCharge_packing_doubleColumn_le
    [Fintype Row]
    {R C : ℝ} (hR : 0 < R) (hC : 0 ≤ C)
    (a : Row → Source → State → ℝ)
    (lambda : Source → State → ℝ)
    (hlambda : ∀ i j, 0 ≤ lambda i j)
    (ha0 : ∀ r i j, 0 ≤ a r i j)
    (ha1 : ∀ r i j, a r i j ≤ 1)
    (hmean : ∀ r,
      weightedMean lambda (a r) ≤ (1 + packingTheta R C) * R)
    (hcolumn : ∀ i, ∑ r, sourceMean lambda (a r) i ≤ 2 * C)
    (i : Source) :
    (∑ r, expSourceCharge (packingTheta R C) (packingThreshold R C)
      (a r) lambda i) ≤ packingTheta R C / 4 := by
  let factor := 2 * packingTheta R C / (2 + 16 * C)
  have hfactor0 : 0 ≤ factor := by
    dsimp [factor]
    exact div_nonneg
      (mul_nonneg (by norm_num) (packingTheta_nonneg hR hC)) (by linarith)
  calc
    (∑ r, expSourceCharge (packingTheta R C) (packingThreshold R C)
        (a r) lambda i) ≤
        ∑ r, sourceMean lambda (a r) i * factor := by
      exact Finset.sum_le_sum fun r _ ↦ by
        simpa [factor] using expSourceCharge_packing_le hR hC hlambda
          (ha0 r) (ha1 r) (hmean r) i
    _ = (∑ r, sourceMean lambda (a r) i) * factor := by
      rw [Finset.sum_mul]
    _ ≤ (2 * C) * factor :=
      mul_le_mul_of_nonneg_right (hcolumn i) hfactor0
    _ = factor * (2 * C) := by ring
    _ ≤ packingTheta R C / 4 := by
      simpa [factor] using packingSourceDoubleColumnFactor_le hR hC

/-- Capping the exponential hitting weights preserves the one-half
self-charge bound. -/
theorem cappedExpSelfCharge_packing_le_half
    {R C : ℝ} (hR : 0 < R) (hC : 0 ≤ C)
    {a lambda : Source → State → ℝ}
    (hlambda : ∀ i j, 0 ≤ lambda i j)
    (ha0 : ∀ i j, 0 ≤ a i j)
    (ha1 : ∀ i j, a i j ≤ 1)
    (hmean : weightedMean lambda a ≤ (1 + packingTheta R C) * R) :
    cappedExpSelfCharge (packingTheta R C) (packingThreshold R C) a lambda ≤
      1 / 2 :=
  (cappedExpSelfCharge_le _ _ _ hlambda).trans
    (expSelfCharge_packing_le_half hR hC hlambda ha0 ha1 hmean)

/-- The capped source charges inherit the `theta / 4` double-column bound. -/
theorem sum_cappedExpSourceCharge_packing_doubleColumn_le
    [Fintype Row]
    {R C : ℝ} (hR : 0 < R) (hC : 0 ≤ C)
    (a : Row → Source → State → ℝ)
    (lambda : Source → State → ℝ)
    (hlambda : ∀ i j, 0 ≤ lambda i j)
    (ha0 : ∀ r i j, 0 ≤ a r i j)
    (ha1 : ∀ r i j, a r i j ≤ 1)
    (hmean : ∀ r,
      weightedMean lambda (a r) ≤ (1 + packingTheta R C) * R)
    (hcolumn : ∀ i, ∑ r, sourceMean lambda (a r) i ≤ 2 * C)
    (i : Source) :
    (∑ r, cappedExpSourceCharge (packingTheta R C) (packingThreshold R C)
      (a r) lambda i) ≤ packingTheta R C / 4 := by
  calc
    (∑ r, cappedExpSourceCharge (packingTheta R C) (packingThreshold R C)
        (a r) lambda i) ≤
        ∑ r, expSourceCharge (packingTheta R C) (packingThreshold R C)
          (a r) lambda i := by
      exact Finset.sum_le_sum fun r _ ↦
        cappedExpSourceCharge_le _ _ (a r) hlambda i
    _ ≤ packingTheta R C / 4 :=
      sum_expSourceCharge_packing_doubleColumn_le hR hC a lambda hlambda
        ha0 ha1 hmean hcolumn i

end WeightedEdgeColoring.FinitePartialResamplingNumerics
