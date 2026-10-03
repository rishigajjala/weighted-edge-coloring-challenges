import WeightedEdgeColoring.FiniteCategoricalInflation
import WeightedEdgeColoring.FinitePartialResamplingCriterionArithmetic
import WeightedEdgeColoring.FinitePartialResamplingCoarseCriterion
import WeightedEdgeColoring.FinitePartialResamplingProcess

/-!
# Packing rows satisfy the coarse partial-resampling charge criterion

This file joins the exponential packing estimates to the abstract coarse
witness-tree criterion.  It also records that the capped exponential weights
hit every row whose load reaches the packing threshold.
-/

namespace WeightedEdgeColoring.FinitePartialResamplingPackingCharges

open scoped BigOperators
open WeightedEdgeColoring.FinitePartialResamplingExponential
open WeightedEdgeColoring.FinitePartialResamplingNumerics
open WeightedEdgeColoring.FiniteCategoricalInflation
open WeightedEdgeColoring.FinitePartialResamplingNeighborPolynomial
open WeightedEdgeColoring.FinitePartialResamplingProcess

variable {Source State Row : Type*}
variable [Fintype Source] [DecidableEq Source]
variable [Fintype State] [DecidableEq State]
variable [Fintype Row] [DecidableEq Row]

/-- The capped exponential weight used for one packing row. -/
noncomputable def packingHittingWeight (R C : ℝ)
    (a : Row → Source → State → ℝ)
    (r : Row) (Y : PartialAssignment Source State) : ℝ :=
  cappedExpHittingWeight (packingTheta R C) (packingThreshold R C)
    (a r) Y

/-- The coarse self charge is definitionally the capped exponential self
charge of the corresponding row. -/
theorem coarseSelfCharge_packingHittingWeight
    (R C : ℝ) (a : Row → Source → State → ℝ)
    (lambda : Source → State → ℝ) (r : Row) :
    coarseSelfCharge (packingHittingWeight R C a) lambda r =
      cappedExpSelfCharge (packingTheta R C) (packingThreshold R C)
        (a r) lambda := by
  rfl

/-- The coarse source charge is the capped exponential source charge. -/
theorem coarseSourceCharge_packingHittingWeight
    (R C : ℝ) (a : Row → Source → State → ℝ)
    (lambda : Source → State → ℝ) (r : Row) (i : Source) :
    coarseSourceCharge (packingHittingWeight R C a) lambda r i =
      cappedExpSourceCharge (packingTheta R C) (packingThreshold R C)
        (a r) lambda i := by
  classical
  unfold coarseSourceCharge cappedExpSourceCharge UsesSource
  apply Finset.sum_congr rfl
  intro Y _hY
  by_cases hnone : Y i = none
  · simp [hnone]
  · simp [hnone, packingHittingWeight]

theorem packingHittingWeight_nonneg
    {R C : ℝ} (hR : 0 < R) (hC : 0 ≤ C)
    {a : Row → Source → State → ℝ}
    (ha0 : ∀ r i j, 0 ≤ a r i j) :
    ∀ r Y, 0 ≤ packingHittingWeight R C a r Y := by
  intro r Y
  exact cappedExpHittingWeight_nonneg
    (packingTheta_pos hR hC) (packingThreshold_pos hR hC) (ha0 r) Y

theorem cappedExpSourceCharge_nonneg
    {theta threshold : ℝ}
    {a lambda : Source → State → ℝ}
    (hq : ∀ Y, 0 ≤ cappedExpHittingWeight theta threshold a Y)
    (hlambda : ∀ i j, 0 ≤ lambda i j) (i : Source) :
    0 ≤ cappedExpSourceCharge theta threshold a lambda i := by
  unfold cappedExpSourceCharge
  apply Finset.sum_nonneg
  intro Y _hY
  by_cases hnone : Y i = none
  · simp [hnone]
  · simp only [hnone, if_false]
    apply mul_nonneg (hq Y)
    unfold partialLambdaProduct partialProduct
    apply Finset.prod_nonneg
    intro source _hsource
    cases hstate : Y source with
    | none => simp [hstate]
    | some state => simpa [hstate] using hlambda source state

/-- Inflation has exactly the coordinatewise scaling required in the lambda
substitution. -/
theorem inflatedMass_eq_lambdaTotal_mul
    {theta : ℝ} {p : Source → State → ℝ}
    (hp_sum : ∀ i, ∑ j, p i j = 1) (i : Source) (j : State) :
    inflatedMass theta p i j =
      lambdaTotal (inflatedMass theta p) i * p i j := by
  unfold lambdaTotal
  rw [sum_inflatedMass hp_sum i]
  rfl

/-- The proved half-self-charge and quarter-source-charge bounds satisfy the
full coarse lambda criterion for every packing row. -/
theorem packing_coarse_charge_criterion
    {R C : ℝ} (hR : 0 < R) (hC : 0 ≤ C)
    (p : Source → State → ℝ)
    (a : Row → Source → State → ℝ)
    (hp : ∀ i j, 0 ≤ p i j)
    (hp_sum : ∀ i, ∑ j, p i j = 1)
    (ha0 : ∀ r i j, 0 ≤ a r i j)
    (ha1 : ∀ r i j, a r i j ≤ 1)
    (hmean : ∀ r, weightedMean p (a r) ≤ R)
    (hcolumn : ∀ i j, ∑ r, a r i j ≤ C) :
    (∀ r,
      coarseSelfCharge (packingHittingWeight R C a)
        (inflatedMass (packingTheta R C) p) r < 1) ∧
    (∀ i,
      (∑ r,
        coarseSourceCharge (packingHittingWeight R C a)
            (inflatedMass (packingTheta R C) p) r i /
          (1 - coarseSelfCharge (packingHittingWeight R C a)
            (inflatedMass (packingTheta R C) p) r)) ≤
        lambdaTotal (inflatedMass (packingTheta R C) p) i - 1) := by
  let theta := packingTheta R C
  let threshold := packingThreshold R C
  let lambda := inflatedMass theta p
  let q := packingHittingWeight R C a
  have hselfHalf : ∀ r,
      cappedExpSelfCharge theta threshold (a r) lambda ≤ 1 / 2 := by
    intro r
    exact cappedExpSelfCharge_packing_le_half hR hC
      (inflatedMass_nonneg (packingTheta_nonneg hR hC) hp)
      (ha0 r) (ha1 r)
      (weightedMean_inflatedMass_le
        (packingTheta_nonneg hR hC) (hmean r))
  have hsourceSum : ∀ i,
      (∑ r, cappedExpSourceCharge theta threshold (a r) lambda i) ≤
        theta / 4 := by
    intro i
    exact sum_cappedExpSourceCharge_inflatedProbability_le hR hC p a hp
      hp_sum ha0 ha1 hmean hcolumn i
  have hq0 : ∀ r Y, 0 ≤ q r Y := by
    intro r Y
    exact packingHittingWeight_nonneg hR hC ha0 r Y
  have hlambda0 : ∀ i j, 0 ≤ lambda i j :=
    inflatedMass_nonneg (packingTheta_nonneg hR hC) hp
  have hsource0 : ∀ r i,
      0 ≤ cappedExpSourceCharge theta threshold (a r) lambda i := by
    intro r i
    exact cappedExpSourceCharge_nonneg (fun Y ↦ hq0 r Y) hlambda0 i
  have harithmetic := packing_lambda_criterion_arithmetic hR hC
    (fun r ↦ cappedExpSelfCharge theta threshold (a r) lambda)
    (fun r i ↦ cappedExpSourceCharge theta threshold (a r) lambda i)
    hselfHalf hsource0 hsourceSum
  constructor
  · intro r
    rw [coarseSelfCharge_packingHittingWeight]
    exact lt_of_le_of_lt (hselfHalf r) (by norm_num)
  · intro i
    have hi := harithmetic i
    rw [show lambdaTotal lambda i = 1 + theta by
      unfold lambdaTotal lambda theta
      exact sum_inflatedMass hp_sum i]
    simp only [q, lambda, theta, threshold] at hi ⊢
    rw [show (∑ r,
        coarseSourceCharge (packingHittingWeight R C a)
            (inflatedMass (packingTheta R C) p) r i /
          (1 - coarseSelfCharge (packingHittingWeight R C a)
            (inflatedMass (packingTheta R C) p) r)) =
        ∑ r,
          cappedExpSourceCharge (packingTheta R C)
              (packingThreshold R C) (a r)
              (inflatedMass (packingTheta R C) p) i /
            (1 - cappedExpSelfCharge (packingTheta R C)
              (packingThreshold R C) (a r)
              (inflatedMass (packingTheta R C) p)) by
      apply Finset.sum_congr rfl
      intro r _hr
      rw [coarseSourceCharge_packingHittingWeight,
        coarseSelfCharge_packingHittingWeight]]
    linarith

/-- A row at or above the packing threshold has compatible capped hitting
weight at least one. -/
theorem packingHittingWeight_hits_bad_row
    {R C : ℝ} (hR : 0 < R) (hC : 0 ≤ C)
    {a : Row → Source → State → ℝ}
    (ha0 : ∀ r i j, 0 ≤ a r i j)
    (r : Row) (z : Source → State)
    (hbad : packingThreshold R C ≤ ∑ i, a r i (z i)) :
    1 ≤ compatiblePatchTotal (packingHittingWeight R C a) r z := by
  simpa [compatiblePatchTotal, compatiblePatchWeight,
    packingHittingWeight] using
    (sum_cappedExpHittingWeight_compatible_ge_one z
      (packingTheta_pos hR hC) (packingThreshold_pos hR hC)
      (ha0 r) hbad)

end WeightedEdgeColoring.FinitePartialResamplingPackingCharges
