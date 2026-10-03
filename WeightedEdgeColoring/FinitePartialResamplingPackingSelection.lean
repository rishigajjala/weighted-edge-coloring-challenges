import WeightedEdgeColoring.FiniteCategoricalSelection
import WeightedEdgeColoring.FinitePartialResamplingPackingCharges
import WeightedEdgeColoring.FinitePartialResamplingCriterion

/-!
# Finite categorical packing selection by partial resampling

The finite partial-resampling criterion is applied to the capped exponential
hitting weights.  Its charge hypotheses are exactly the packing charge
inequalities, while every row at the forbidden threshold is hit with total
compatible weight at least one.
-/

namespace WeightedEdgeColoring.FiniteCategoricalSelection

open scoped BigOperators
open WeightedEdgeColoring.FinitePartialResamplingExponential
open WeightedEdgeColoring.FinitePartialResamplingNumerics
open WeightedEdgeColoring.FiniteCategoricalInflation
open WeightedEdgeColoring.FinitePartialResamplingNeighborPolynomial
open WeightedEdgeColoring.FinitePartialResamplingProcess
open WeightedEdgeColoring.FinitePartialResamplingPackingCharges
open WeightedEdgeColoring.FinitePartialResamplingCriterion

noncomputable section

variable {Source State Row : Type*}
variable [Fintype Source] [DecidableEq Source]
variable [Fintype State] [DecidableEq State]
variable [Fintype Row] [DecidableEq Row]

/-! ## Zero-charge rows forcing support -/

/-- The partial assignment which names state `a` only at source `i`. -/
private def supportSingleton (i : Source) (a : State) :
    PartialAssignment Source State :=
  fun j ↦ if j = i then some a else none

/-- A support row has weight one precisely on a singleton assignment which
names a zero-probability state at its distinguished source. -/
private noncomputable def zeroMassHittingWeight
    (prob : Source → State → ℝ)
    (i : Source) (Y : PartialAssignment Source State) : ℝ :=
  if ∃ a, prob i a = 0 ∧ Y = supportSingleton i a then 1 else 0

private theorem zeroMassHittingWeight_nonneg
    (prob : Source → State → ℝ) :
    ∀ i Y, 0 ≤ zeroMassHittingWeight prob i Y := by
  intro i Y
  unfold zeroMassHittingWeight
  split <;> norm_num

private theorem zeroMassHittingWeight_empty
    (prob : Source → State → ℝ) (i : Source) :
    zeroMassHittingWeight prob i emptyPartial = 0 := by
  classical
  unfold zeroMassHittingWeight
  rw [if_neg]
  rintro ⟨a, _ha, heq⟩
  have hi := congrFun heq i
  simp [emptyPartial, supportSingleton] at hi

private theorem supportSingleton_compatible
    (i : Source) (z : Source → State) :
    Compatible (supportSingleton i (z i)) z := by
  intro j a hja
  by_cases hji : j = i
  · subst j
    simpa [supportSingleton] using hja
  · simp [supportSingleton, hji] at hja

private theorem zeroMassHittingWeight_hits
    (prob : Source → State → ℝ)
    (i : Source) (z : Source → State)
    (hzero : prob i (z i) = 0) :
    1 ≤ compatiblePatchTotal (zeroMassHittingWeight prob) i z := by
  classical
  let Y : PartialAssignment Source State := supportSingleton i (z i)
  have hweight : ∀ j Z, 0 ≤ zeroMassHittingWeight prob j Z :=
    zeroMassHittingWeight_nonneg prob
  have hcompat : Compatible Y z := supportSingleton_compatible i z
  have hvalue : zeroMassHittingWeight prob i Y = 1 := by
    unfold zeroMassHittingWeight
    rw [if_pos]
    exact ⟨z i, hzero, rfl⟩
  calc
    1 = compatiblePatchWeight (zeroMassHittingWeight prob) i z Y := by
      simp [compatiblePatchWeight, hcompat, hvalue]
    _ ≤ compatiblePatchTotal (zeroMassHittingWeight prob) i z := by
      unfold compatiblePatchTotal
      exact Finset.single_le_sum
        (fun Z _hZ ↦ compatiblePatchWeight_nonneg hweight i z Z)
        (Finset.mem_univ Y)

/-- Every nonzero support-row term contains a zero lambda coordinate. -/
private theorem zeroMassHittingWeight_mul_partialLambdaProduct
    {prob lambda : Source → State → ℝ}
    (hscale : ∀ i a,
      lambda i a = lambdaTotal lambda i * prob i a)
    (i : Source) (Y : PartialAssignment Source State) :
    zeroMassHittingWeight prob i Y * partialLambdaProduct lambda Y = 0 := by
  classical
  unfold zeroMassHittingWeight
  split
  · rename_i hexists
    obtain ⟨a, hprobZero, rfl⟩ := hexists
    have hlambdaZero : lambda i a = 0 := by
      rw [hscale i a, hprobZero, mul_zero]
    have hproduct :
        partialLambdaProduct lambda (supportSingleton i a) = 0 := by
      unfold partialLambdaProduct partialProduct
      apply Finset.prod_eq_zero (Finset.mem_univ i)
      simp [supportSingleton, hlambdaZero]
    simp [hproduct]
  · simp

private theorem coarseSelfCharge_zeroMassHittingWeight
    {prob lambda : Source → State → ℝ}
    (hscale : ∀ i a,
      lambda i a = lambdaTotal lambda i * prob i a)
    (i : Source) :
    coarseSelfCharge (zeroMassHittingWeight prob) lambda i = 0 := by
  unfold coarseSelfCharge
  apply Finset.sum_eq_zero
  intro Y _hY
  exact zeroMassHittingWeight_mul_partialLambdaProduct hscale i Y

private theorem coarseSourceCharge_zeroMassHittingWeight
    {prob lambda : Source → State → ℝ}
    (hscale : ∀ i a,
      lambda i a = lambdaTotal lambda i * prob i a)
    (supportSource queriedSource : Source) :
    coarseSourceCharge (zeroMassHittingWeight prob) lambda
      supportSource queriedSource = 0 := by
  unfold coarseSourceCharge
  apply Finset.sum_eq_zero
  intro Y _hY
  by_cases huses : UsesSource Y queriedSource
  · simp only [huses, if_true]
    exact zeroMassHittingWeight_mul_partialLambdaProduct
      hscale supportSource Y
  · simp [huses]

/-- Add one support-enforcing row per source to the packing hitting family. -/
private noncomputable def supportedPackingWeight
    (R C : ℝ) (prob : Source → State → ℝ)
    (coefficients : Row → Source → State → ℝ) :
    (Row ⊕ Source) → PartialAssignment Source State → ℝ
  | Sum.inl r => packingHittingWeight R C coefficients r
  | Sum.inr i => zeroMassHittingWeight prob i

/-- A combined row is bad either because an original packing row is
overloaded or because one source chose a zero-mass state. -/
private def supportedPackingBad
    (R C : ℝ) (prob : Source → State → ℝ)
    (use : Source → State → Row → ℝ) :
    (Row ⊕ Source) → (Source → State) → Prop
  | Sum.inl r, choice =>
      packingThreshold R C ≤ rowLoad use r choice
  | Sum.inr i, choice => prob i (choice i) = 0

/-- A finite categorical packing instance has a complete choice whose every
row load is strictly below the partial-resampling threshold. -/
theorem exists_choice_rowLoad_lt_packingThreshold
    (R C : ℝ) (hR : 0 < R) (hC : 0 ≤ C)
    (prob : Source → State → ℝ)
    (use : Source → State → Row → ℝ)
    (hprob0 : ∀ i a, 0 ≤ prob i a)
    (hprobSum : ∀ i, ∑ a, prob i a = 1)
    (huse0 : ∀ i a r, 0 ≤ use i a r)
    (huse1 : ∀ i a r, use i a r ≤ 1)
    (hmean : ∀ r, rowMean prob use r ≤ R)
    (hcolumn : ∀ i a, ∑ r, use i a r ≤ C) :
    ∃ choice : Source → State, ∀ r,
      rowLoad use r choice < packingThreshold R C := by
  let coefficients : Row → Source → State → ℝ :=
    fun r i a ↦ use i a r
  let theta := packingTheta R C
  let lambda : Source → State → ℝ :=
    inflatedMass theta prob
  let weight : Row → PartialAssignment Source State → ℝ :=
    packingHittingWeight R C coefficients
  let bad : Row → (Source → State) → Prop :=
    fun r choice ↦ packingThreshold R C ≤ rowLoad use r choice
  have hcoeff0 : ∀ r i a, 0 ≤ coefficients r i a := by
    intro r i a
    exact huse0 i a r
  have hcoeff1 : ∀ r i a, coefficients r i a ≤ 1 := by
    intro r i a
    exact huse1 i a r
  have hweightedMean :
      ∀ r, weightedMean prob (coefficients r) ≤ R := by
    intro r
    simpa [coefficients, weightedMean, rowMean] using hmean r
  have hcoefficientColumn :
      ∀ i a, ∑ r, coefficients r i a ≤ C := by
    intro i a
    simpa [coefficients] using hcolumn i a
  have hweight : ∀ r Y, 0 ≤ weight r Y := by
    intro r Y
    exact packingHittingWeight_nonneg hR hC hcoeff0 r Y
  have hempty : ∀ r, weight r emptyPartial = 0 := by
    intro r
    simp [weight, packingHittingWeight, cappedExpHittingWeight,
      expHittingWeight]
  have hlambda : ∀ i a, 0 ≤ lambda i a := by
    exact inflatedMass_nonneg (packingTheta_nonneg hR hC) hprob0
  have hscale : ∀ i a,
      lambda i a = lambdaTotal lambda i * prob i a := by
    intro i a
    simpa [lambda, theta] using
      (inflatedMass_eq_lambdaTotal_mul
        (theta := packingTheta R C) hprobSum i a)
  obtain ⟨hself, hsource⟩ :=
    packing_coarse_charge_criterion hR hC prob coefficients hprob0
      hprobSum hcoeff0 hcoeff1 hweightedMean hcoefficientColumn
  have hhit : ∀ r choice, bad r choice →
      1 ≤ compatiblePatchTotal weight r choice := by
    intro r choice hbad
    exact packingHittingWeight_hits_bad_row hR hC hcoeff0 r choice
      (by simpa [bad, rowLoad, coefficients] using hbad)
  obtain ⟨choice, hchoice⟩ := exists_completeState_avoiding_badRows
    prob lambda hprob0 hprobSum hlambda hscale weight hweight hempty bad
    hhit (by simpa [weight, lambda, theta, coefficients] using hself)
    (by simpa [weight, lambda, theta, coefficients] using hsource)
  refine ⟨choice, ?_⟩
  intro r
  simpa [bad, not_le] using hchoice r

/-- Support-preserving form of the packing selector.  Besides satisfying the
same row threshold, every chosen state has strictly positive categorical
mass.  The additional support rows have exactly zero lambda charge, so the
packing threshold and its column parameter are unchanged. -/
theorem exists_supported_choice_rowLoad_lt_packingThreshold
    (R C : ℝ) (hR : 0 < R) (hC : 0 ≤ C)
    (prob : Source → State → ℝ)
    (use : Source → State → Row → ℝ)
    (hprob0 : ∀ i a, 0 ≤ prob i a)
    (hprobSum : ∀ i, ∑ a, prob i a = 1)
    (huse0 : ∀ i a r, 0 ≤ use i a r)
    (huse1 : ∀ i a r, use i a r ≤ 1)
    (hmean : ∀ r, rowMean prob use r ≤ R)
    (hcolumn : ∀ i a, ∑ r, use i a r ≤ C) :
    ∃ choice : Source → State,
      (∀ i, 0 < prob i (choice i)) ∧
      ∀ r, rowLoad use r choice < packingThreshold R C := by
  let coefficients : Row → Source → State → ℝ :=
    fun r i a ↦ use i a r
  let theta := packingTheta R C
  let lambda : Source → State → ℝ :=
    inflatedMass theta prob
  let weight : (Row ⊕ Source) →
      PartialAssignment Source State → ℝ :=
    supportedPackingWeight R C prob coefficients
  let bad : (Row ⊕ Source) → (Source → State) → Prop :=
    supportedPackingBad R C prob use
  have hcoeff0 : ∀ r i a, 0 ≤ coefficients r i a := by
    intro r i a
    exact huse0 i a r
  have hcoeff1 : ∀ r i a, coefficients r i a ≤ 1 := by
    intro r i a
    exact huse1 i a r
  have hweightedMean :
      ∀ r, weightedMean prob (coefficients r) ≤ R := by
    intro r
    simpa [coefficients, weightedMean, rowMean] using hmean r
  have hcoefficientColumn :
      ∀ i a, ∑ r, coefficients r i a ≤ C := by
    intro i a
    simpa [coefficients] using hcolumn i a
  have hlambda : ∀ i a, 0 ≤ lambda i a := by
    exact inflatedMass_nonneg (packingTheta_nonneg hR hC) hprob0
  have hscale : ∀ i a,
      lambda i a = lambdaTotal lambda i * prob i a := by
    intro i a
    simpa [lambda, theta] using
      (inflatedMass_eq_lambdaTotal_mul
        (theta := packingTheta R C) hprobSum i a)
  obtain ⟨hpackingSelf, hpackingSource⟩ :=
    packing_coarse_charge_criterion hR hC prob coefficients hprob0
      hprobSum hcoeff0 hcoeff1 hweightedMean hcoefficientColumn
  have hweight : ∀ row Y, 0 ≤ weight row Y := by
    intro row Y
    cases row with
    | inl r =>
        exact packingHittingWeight_nonneg hR hC hcoeff0 r Y
    | inr i =>
        exact zeroMassHittingWeight_nonneg prob i Y
  have hempty : ∀ row, weight row emptyPartial = 0 := by
    intro row
    cases row with
    | inl r =>
        simp [weight, supportedPackingWeight, packingHittingWeight,
          cappedExpHittingWeight, expHittingWeight]
    | inr i =>
        exact zeroMassHittingWeight_empty prob i
  have hhit : ∀ row choice, bad row choice →
      1 ≤ compatiblePatchTotal weight row choice := by
    intro row choice hbad
    cases row with
    | inl r =>
        exact packingHittingWeight_hits_bad_row hR hC hcoeff0 r choice
          (by simpa [bad, supportedPackingBad, rowLoad, coefficients]
            using hbad)
    | inr i =>
        exact zeroMassHittingWeight_hits prob i choice
          (by simpa [bad, supportedPackingBad] using hbad)
  have hself : ∀ row, coarseSelfCharge weight lambda row < 1 := by
    intro row
    cases row with
    | inl r =>
        simpa [weight, supportedPackingWeight, lambda, theta,
          coefficients] using hpackingSelf r
    | inr i =>
        have hzero := coarseSelfCharge_zeroMassHittingWeight hscale i
        have hzero' : coarseSelfCharge weight lambda (Sum.inr i) = 0 := by
          simpa [weight, supportedPackingWeight] using hzero
        rw [hzero']
        norm_num
  have hsource : ∀ queriedSource,
      (∑ row, coarseSourceCharge weight lambda row queriedSource /
        (1 - coarseSelfCharge weight lambda row)) ≤
          lambdaTotal lambda queriedSource - 1 := by
    intro queriedSource
    rw [Fintype.sum_sum_type]
    have hsupport :
        (∑ supportSource : Source,
          coarseSourceCharge weight lambda (Sum.inr supportSource)
              queriedSource /
            (1 - coarseSelfCharge weight lambda
              (Sum.inr supportSource))) = 0 := by
      apply Finset.sum_eq_zero
      intro supportSource _hsupportSource
      have hsourceZero := coarseSourceCharge_zeroMassHittingWeight
        hscale supportSource queriedSource
      have hselfZero := coarseSelfCharge_zeroMassHittingWeight
        hscale supportSource
      change
        coarseSourceCharge (zeroMassHittingWeight prob) lambda
              supportSource queriedSource /
            (1 - coarseSelfCharge (zeroMassHittingWeight prob) lambda
              supportSource) = 0
      rw [hsourceZero, hselfZero]
      norm_num
    rw [hsupport, add_zero]
    simpa [weight, supportedPackingWeight, lambda, theta, coefficients] using
      hpackingSource queriedSource
  obtain ⟨choice, hchoice⟩ := exists_completeState_avoiding_badRows
    prob lambda hprob0 hprobSum hlambda hscale weight hweight hempty bad
    hhit hself hsource
  refine ⟨choice, ?_, ?_⟩
  · intro i
    have hne : prob i (choice i) ≠ 0 := by
      intro hzero
      exact hchoice (Sum.inr i)
        (by simpa [bad, supportedPackingBad] using hzero)
    exact lt_of_le_of_ne (hprob0 i (choice i)) hne.symm
  · intro r
    simpa [bad, supportedPackingBad, not_le] using hchoice (Sum.inl r)

end

end WeightedEdgeColoring.FiniteCategoricalSelection
