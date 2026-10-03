import WeightedEdgeColoring.FinitePartialResamplingExponential

/-!
# Capping the exponential fractional hitting weights

The exponential formula can assign a number larger than one to a partial
assignment.  The partial-resampling theorem is usually stated for weights in
`[0,1]`.  Capping every weight at one preserves the hitting property: if an
uncapped term is already at least one, its cap alone pays the full unit; if no
term reaches one, capping changes nothing.  It can only lower every charge.
-/

namespace WeightedEdgeColoring.FinitePartialResamplingExponential

open scoped BigOperators

variable {Source State : Type*}
variable [Fintype Source] [DecidableEq Source]
variable [Fintype State] [DecidableEq State]

/-- Exponential hitting weight capped into the interval `[0,1]`. -/
noncomputable def cappedExpHittingWeight (theta threshold : ℝ)
    (a : Source → State → ℝ) (Y : PartialAssignment Source State) : ℝ :=
  min 1 (expHittingWeight theta threshold a Y)

private theorem partialProduct_nonneg
    {term : Source → State → ℝ} (hterm : ∀ i j, 0 ≤ term i j)
    (Y : PartialAssignment Source State) :
    0 ≤ partialProduct term Y := by
  unfold partialProduct
  apply Finset.prod_nonneg
  intro i _hi
  cases hYi : Y i with
  | none => simp
  | some j => simpa [hYi] using hterm i j

theorem expHittingWeight_nonneg
    {theta threshold : ℝ} {a : Source → State → ℝ}
    (htheta : 0 < theta) (hthreshold : 0 < threshold)
    (ha0 : ∀ i j, 0 ≤ a i j) (Y : PartialAssignment Source State) :
    0 ≤ expHittingWeight theta threshold a Y := by
  have hden : 0 < Real.exp (theta * threshold) - 1 :=
    sub_pos.mpr (Real.one_lt_exp_iff.mpr (mul_pos htheta hthreshold))
  unfold expHittingWeight
  split_ifs
  · norm_num
  · exact div_nonneg
      (partialProduct_nonneg (expKernel_nonneg htheta.le ha0) Y) hden.le

theorem cappedExpHittingWeight_nonneg
    {theta threshold : ℝ} {a : Source → State → ℝ}
    (htheta : 0 < theta) (hthreshold : 0 < threshold)
    (ha0 : ∀ i j, 0 ≤ a i j) (Y : PartialAssignment Source State) :
    0 ≤ cappedExpHittingWeight theta threshold a Y := by
  exact le_min zero_le_one (expHittingWeight_nonneg htheta hthreshold ha0 Y)

theorem cappedExpHittingWeight_le_one
    (theta threshold : ℝ) (a : Source → State → ℝ)
    (Y : PartialAssignment Source State) :
    cappedExpHittingWeight theta threshold a Y ≤ 1 := by
  exact min_le_left _ _

theorem cappedExpHittingWeight_le
    (theta threshold : ℝ) (a : Source → State → ℝ)
    (Y : PartialAssignment Source State) :
    cappedExpHittingWeight theta threshold a Y ≤
      expHittingWeight theta threshold a Y := by
  exact min_le_right _ _

/-- A finite family with total mass at least one still has total mass at least
one after every term is capped at one. -/
theorem one_le_sum_min_one
    {α : Type*} [Fintype α] [DecidableEq α]
    (f : α → ℝ) (hf : ∀ x, 0 ≤ f x) (hsum : 1 ≤ ∑ x, f x) :
    1 ≤ ∑ x, min 1 (f x) := by
  classical
  by_cases hlarge : ∃ x, 1 ≤ f x
  · obtain ⟨x, hx⟩ := hlarge
    calc
      1 = min 1 (f x) := (min_eq_left hx).symm
      _ ≤ ∑ y : α, min 1 (f y) := by
        exact Finset.single_le_sum
          (fun y _hy ↦ le_min zero_le_one (hf y)) (Finset.mem_univ x)
  · have hsmall : ∀ x, f x ≤ 1 := by
      intro x
      exact le_of_not_ge fun hx ↦ hlarge ⟨x, hx⟩
    simpa [min_eq_right (hsmall _)] using hsum

/-- The capped weights retain the exponential hitting property. -/
theorem sum_cappedExpHittingWeight_compatible_ge_one
    {theta threshold : ℝ} {a : Source → State → ℝ} (z : Source → State)
    (htheta : 0 < theta) (hthreshold : 0 < threshold)
    (ha0 : ∀ i j, 0 ≤ a i j)
    (hbad : threshold ≤ ∑ i, a i (z i)) :
    1 ≤ ∑ Y : PartialAssignment Source State,
      if Compatible Y z then cappedExpHittingWeight theta threshold a Y else 0 := by
  let f : PartialAssignment Source State → ℝ := fun Y ↦
    if Compatible Y z then expHittingWeight theta threshold a Y else 0
  have hf : ∀ Y, 0 ≤ f Y := by
    intro Y
    by_cases hcompat : Compatible Y z
    · simp [f, hcompat, expHittingWeight_nonneg htheta hthreshold ha0 Y]
    · simp [f, hcompat]
  have hsum : 1 ≤ ∑ Y, f Y := by
    simpa [f] using sum_expHittingWeight_compatible_ge_one z htheta
      hthreshold hbad
  have hcapped := one_le_sum_min_one f hf hsum
  calc
    1 ≤ ∑ Y, min 1 (f Y) := hcapped
    _ = ∑ Y : PartialAssignment Source State,
        if Compatible Y z then cappedExpHittingWeight theta threshold a Y
        else 0 := by
      apply Finset.sum_congr rfl
      intro Y _hY
      by_cases hcompat : Compatible Y z <;>
        simp [f, hcompat, cappedExpHittingWeight]

/-- Self-charge formed with capped exponential weights. -/
noncomputable def cappedExpSelfCharge (theta threshold : ℝ)
    (a lambda : Source → State → ℝ) : ℝ :=
  ∑ Y : PartialAssignment Source State,
    cappedExpHittingWeight theta threshold a Y * partialLambdaProduct lambda Y

/-- Source charge formed with capped exponential weights. -/
noncomputable def cappedExpSourceCharge (theta threshold : ℝ)
    (a lambda : Source → State → ℝ) (i : Source) : ℝ :=
  ∑ Y : PartialAssignment Source State,
    if Y i = none then 0
    else cappedExpHittingWeight theta threshold a Y * partialLambdaProduct lambda Y

private theorem partialLambdaProduct_nonneg
    {lambda : Source → State → ℝ} (hlambda : ∀ i j, 0 ≤ lambda i j)
    (Y : PartialAssignment Source State) :
    0 ≤ partialLambdaProduct lambda Y := by
  exact partialProduct_nonneg hlambda Y

theorem cappedExpSelfCharge_le
    (theta threshold : ℝ) (a : Source → State → ℝ)
    {lambda : Source → State → ℝ} (hlambda : ∀ i j, 0 ≤ lambda i j) :
    cappedExpSelfCharge theta threshold a lambda ≤
      expSelfCharge theta threshold a lambda := by
  unfold cappedExpSelfCharge expSelfCharge
  exact Finset.sum_le_sum fun Y _hY ↦
    mul_le_mul_of_nonneg_right
      (cappedExpHittingWeight_le theta threshold a Y)
      (partialLambdaProduct_nonneg hlambda Y)

theorem cappedExpSourceCharge_le
    (theta threshold : ℝ) (a : Source → State → ℝ)
    {lambda : Source → State → ℝ} (hlambda : ∀ i j, 0 ≤ lambda i j)
    (i : Source) :
    cappedExpSourceCharge theta threshold a lambda i ≤
      expSourceCharge theta threshold a lambda i := by
  unfold cappedExpSourceCharge expSourceCharge
  apply Finset.sum_le_sum
  intro Y _hY
  by_cases hnone : Y i = none
  · simp [hnone]
  · simp only [hnone, ↓reduceIte]
    exact mul_le_mul_of_nonneg_right
      (cappedExpHittingWeight_le theta threshold a Y)
      (partialLambdaProduct_nonneg hlambda Y)

end WeightedEdgeColoring.FinitePartialResamplingExponential
