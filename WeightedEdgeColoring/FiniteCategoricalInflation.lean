import WeightedEdgeColoring.FinitePartialResamplingChargeBounds

/-!
# Inflating a finite categorical probability law

This file connects an ordinary categorical probability law `p` to the
inflated mass used by the finite partial-resampling estimates.  For

`lambda i j = (1 + theta) * p i j`,

every row mean is multiplied by exactly `1 + theta`.  If the coefficients in
each source--state column sum to at most `C`, normalization of `p` gives a
source-mean bound `(1 + theta) * C`, and hence the simpler bound `2 * C` when
`0 <= theta <= 1`.  The final theorem feeds these two facts directly into the
capped source-charge estimate.
-/

namespace WeightedEdgeColoring.FiniteCategoricalInflation

open scoped BigOperators
open WeightedEdgeColoring.FinitePartialResamplingExponential
open WeightedEdgeColoring.FinitePartialResamplingNumerics

variable {Source State Row : Type*}
variable [Fintype Source] [DecidableEq Source]
variable [Fintype State] [DecidableEq State]

/-- Inflate every mass in a categorical law by the common factor
`1 + theta`. -/
def inflatedMass (theta : ℝ) (p : Source → State → ℝ) :
    Source → State → ℝ :=
  fun i j ↦ (1 + theta) * p i j

@[simp] theorem inflatedMass_apply (theta : ℝ)
    (p : Source → State → ℝ) (i : Source) (j : State) :
    inflatedMass theta p i j = (1 + theta) * p i j := rfl

/-- Nonnegative categorical masses stay nonnegative after inflation by a
nonnegative parameter. -/
theorem inflatedMass_nonneg {theta : ℝ} {p : Source → State → ℝ}
    (htheta : 0 ≤ theta) (hp : ∀ i j, 0 ≤ p i j) :
    ∀ i j, 0 ≤ inflatedMass theta p i j := by
  intro i j
  exact mul_nonneg (by linarith) (hp i j)

/-- A normalized categorical probability law has inflated mass
`1 + theta` at every source. -/
theorem sum_inflatedMass {theta : ℝ} {p : Source → State → ℝ}
    (hp_sum : ∀ i, ∑ j, p i j = 1) (i : Source) :
    (∑ j, inflatedMass theta p i j) = 1 + theta := by
  unfold inflatedMass
  rw [← Finset.mul_sum, hp_sum i]
  ring

/-- Inflating the categorical mass scales every row mean by exactly the same
factor. -/
theorem weightedMean_inflatedMass (theta : ℝ)
    (p a : Source → State → ℝ) :
    weightedMean (inflatedMass theta p) a =
      (1 + theta) * weightedMean p a := by
  unfold weightedMean inflatedMass
  calc
    (∑ i, ∑ j, ((1 + theta) * p i j) * a i j) =
        ∑ i, ∑ j, (1 + theta) * (p i j * a i j) := by
      apply Finset.sum_congr rfl
      intro i _hi
      apply Finset.sum_congr rfl
      intro j _hj
      ring
    _ = ∑ i, (1 + theta) * (∑ j, p i j * a i j) := by
      apply Finset.sum_congr rfl
      intro i _hi
      rw [Finset.mul_sum]
    _ = (1 + theta) * (∑ i, ∑ j, p i j * a i j) := by
      rw [Finset.mul_sum]

/-- Inflation scales the part of a row mean carried by one source by exactly
`1 + theta`. -/
theorem sourceMean_inflatedMass (theta : ℝ)
    (p a : Source → State → ℝ) (i : Source) :
    sourceMean (inflatedMass theta p) a i =
      (1 + theta) * sourceMean p a i := by
  unfold sourceMean inflatedMass
  calc
    (∑ j, ((1 + theta) * p i j) * a i j) =
        ∑ j, (1 + theta) * (p i j * a i j) := by
      apply Finset.sum_congr rfl
      intro j _hj
      ring
    _ = (1 + theta) * (∑ j, p i j * a i j) := by
      rw [Finset.mul_sum]

/-- A row bound under `p` scales to the corresponding row bound under the
inflated mass. -/
theorem weightedMean_inflatedMass_le {theta R : ℝ}
    {p a : Source → State → ℝ}
    (htheta : 0 ≤ theta) (hmean : weightedMean p a ≤ R) :
    weightedMean (inflatedMass theta p) a ≤ (1 + theta) * R := by
  rw [weightedMean_inflatedMass]
  exact mul_le_mul_of_nonneg_left hmean (by linarith)

/-- A source--state coefficient-column bound averages to the same bound under
a normalized categorical probability law. -/
theorem sum_sourceMean_le_of_stateColumn
    [Fintype Row]
    {C : ℝ} {p : Source → State → ℝ}
    (a : Row → Source → State → ℝ)
    (hp : ∀ i j, 0 ≤ p i j)
    (hp_sum : ∀ i, ∑ j, p i j = 1)
    (hcolumn : ∀ i j, ∑ r, a r i j ≤ C)
    (i : Source) :
    (∑ r, sourceMean p (a r) i) ≤ C := by
  unfold sourceMean
  calc
    (∑ r, ∑ j, p i j * a r i j) =
        ∑ j, p i j * (∑ r, a r i j) := by
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro j _hj
      rw [Finset.mul_sum]
    _ ≤ ∑ j, p i j * C := by
      exact Finset.sum_le_sum fun j _hj ↦
        mul_le_mul_of_nonneg_left (hcolumn i j) (hp i j)
    _ = (∑ j, p i j) * C := by
      rw [Finset.sum_mul]
    _ = C := by
      rw [hp_sum i]
      ring

/-- Summing inflated source means first and then removing the common factor
is an exact identity. -/
theorem sum_sourceMean_inflatedMass
    [Fintype Row]
    (theta : ℝ) (p : Source → State → ℝ)
    (a : Row → Source → State → ℝ) (i : Source) :
    (∑ r, sourceMean (inflatedMass theta p) (a r) i) =
      (1 + theta) * (∑ r, sourceMean p (a r) i) := by
  calc
    (∑ r, sourceMean (inflatedMass theta p) (a r) i) =
        ∑ r, (1 + theta) * sourceMean p (a r) i := by
      apply Finset.sum_congr rfl
      intro r _hr
      exact sourceMean_inflatedMass theta p (a r) i
    _ = (1 + theta) * (∑ r, sourceMean p (a r) i) := by
      rw [Finset.mul_sum]

/-- If `0 <= theta <= 1`, a source--state column budget `C` becomes a source
budget of at most `2 * C` after inflation. -/
theorem sum_sourceMean_inflatedMass_le_two_mul
    [Fintype Row]
    {theta C : ℝ} {p : Source → State → ℝ}
    (a : Row → Source → State → ℝ)
    (htheta0 : 0 ≤ theta) (htheta1 : theta ≤ 1) (hC : 0 ≤ C)
    (hp : ∀ i j, 0 ≤ p i j)
    (hp_sum : ∀ i, ∑ j, p i j = 1)
    (hcolumn : ∀ i j, ∑ r, a r i j ≤ C)
    (i : Source) :
    (∑ r, sourceMean (inflatedMass theta p) (a r) i) ≤ 2 * C := by
  have hbase : (∑ r, sourceMean p (a r) i) ≤ C :=
    sum_sourceMean_le_of_stateColumn a hp hp_sum hcolumn i
  have hfactor : 0 ≤ 1 + theta := by linarith
  have hgap : 0 ≤ (1 - theta) * C :=
    mul_nonneg (sub_nonneg.mpr htheta1) hC
  calc
    (∑ r, sourceMean (inflatedMass theta p) (a r) i) =
        (1 + theta) * (∑ r, sourceMean p (a r) i) :=
      sum_sourceMean_inflatedMass theta p a i
    _ ≤ (1 + theta) * C :=
      mul_le_mul_of_nonneg_left hbase hfactor
    _ ≤ 2 * C := by nlinarith

/-- For the packing choice of `theta`, normalized categorical probabilities
and source--state column bounds supply exactly the doubled source-column
budget required by the charge theorem. -/
theorem sum_sourceMean_inflatedMass_packing_le_two_mul
    [Fintype Row]
    {R C : ℝ} (hR : 0 < R) (hC : 0 ≤ C)
    {p : Source → State → ℝ}
    (a : Row → Source → State → ℝ)
    (hp : ∀ i j, 0 ≤ p i j)
    (hp_sum : ∀ i, ∑ j, p i j = 1)
    (hcolumn : ∀ i j, ∑ r, a r i j ≤ C)
    (i : Source) :
    (∑ r, sourceMean (inflatedMass (packingTheta R C) p) (a r) i) ≤
      2 * C := by
  exact sum_sourceMean_inflatedMass_le_two_mul a
    (packingTheta_nonneg hR hC) (packingTheta_le_one R C) hC hp hp_sum
    hcolumn i

/-- Practical capped-charge bridge.  Start from a normalized categorical
probability law whose row means are at most `R` and whose source--state
coefficient columns are at most `C`.  Inflate it by the packing factor.  Then
the total capped source charge through every source is at most `theta / 4`. -/
theorem sum_cappedExpSourceCharge_inflatedProbability_le
    [Fintype Row]
    {R C : ℝ} (hR : 0 < R) (hC : 0 ≤ C)
    (p : Source → State → ℝ)
    (a : Row → Source → State → ℝ)
    (hp : ∀ i j, 0 ≤ p i j)
    (hp_sum : ∀ i, ∑ j, p i j = 1)
    (ha0 : ∀ r i j, 0 ≤ a r i j)
    (ha1 : ∀ r i j, a r i j ≤ 1)
    (hmean : ∀ r, weightedMean p (a r) ≤ R)
    (hcolumn : ∀ i j, ∑ r, a r i j ≤ C)
    (i : Source) :
    (∑ r, cappedExpSourceCharge (packingTheta R C)
      (packingThreshold R C) (a r)
      (inflatedMass (packingTheta R C) p) i) ≤
        packingTheta R C / 4 := by
  apply sum_cappedExpSourceCharge_packing_doubleColumn_le hR hC a
    (inflatedMass (packingTheta R C) p)
  · exact inflatedMass_nonneg (packingTheta_nonneg hR hC) hp
  · exact ha0
  · exact ha1
  · intro r
    exact weightedMean_inflatedMass_le
      (packingTheta_nonneg hR hC) (hmean r)
  · intro source
    exact sum_sourceMean_inflatedMass_packing_le_two_mul hR hC a hp hp_sum
      hcolumn source

end WeightedEdgeColoring.FiniteCategoricalInflation
