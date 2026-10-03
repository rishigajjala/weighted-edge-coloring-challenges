import WeightedEdgeColoring.FinitePartialResamplingPackingMeanSelection
import WeightedEdgeColoring.PackingDeviationPolynomialColumn

/-!
# Two-sided mass-sensitive selection for weighted-moment switches

At one Kempe-switch step the independent sources are path-component coins.
Each coordinate to be tracked is a sum of nonnegative contributions.  To
control both signs of its error, the manuscript applies the same selection
theorem to the contribution and to its pointwise cap minus the contribution.

The theorem below packages that argument.  Sparse caps are part of the data:
if a source cannot affect a row its cap is zero.  Consequently the upper and
lower copies together have exactly the cap column mass, rather than twice the
number of rows.  This is the form in which the finite partial-resampling
machinery can be consumed by the Kempe-switch construction.
-/

namespace WeightedEdgeColoring.WeightedMomentTwoSidedSelection

open scoped BigOperators
open WeightedEdgeColoring.FiniteCategoricalSelection
open WeightedEdgeColoring.FinitePartialResamplingNumerics

noncomputable section

variable {Source State Row : Type*}
variable [Fintype Source] [DecidableEq Source]
variable [Fintype State] [DecidableEq State]
variable [Fintype Row] [DecidableEq Row]

/-- Upper and complementary-lower copies of a family of statistics. -/
def signedUse (use : Source → State → Row → ℝ)
    (cap : Source → Row → ℝ) :
    Source → State → (Row × Bool) → ℝ
  | i, a, (r, false) => use i a r
  | i, a, (r, true) => cap i r - use i a r

@[simp] theorem signedUse_false
    (use : Source → State → Row → ℝ) (cap : Source → Row → ℝ)
    (i : Source) (a : State) (r : Row) :
    signedUse use cap i a (r, false) = use i a r := rfl

@[simp] theorem signedUse_true
    (use : Source → State → Row → ℝ) (cap : Source → Row → ℝ)
    (i : Source) (a : State) (r : Row) :
    signedUse use cap i a (r, true) = cap i r - use i a r := rfl

/-- The two signed copies of one source-row contribution add to its cap. -/
theorem signedUse_pair_sum
    (use : Source → State → Row → ℝ) (cap : Source → Row → ℝ)
    (i : Source) (a : State) (r : Row) :
    signedUse use cap i a (r, false) +
        signedUse use cap i a (r, true) = cap i r := by
  simp [signedUse]

/-- Hence the complete signed column mass is exactly the sum of the sparse
caps. -/
theorem sum_signedUse_eq_sum_cap
    (use : Source → State → Row → ℝ) (cap : Source → Row → ℝ)
    (i : Source) (a : State) :
    (∑ sr : Row × Bool, signedUse use cap i a sr) =
      ∑ r : Row, cap i r := by
  rw [Fintype.sum_prod_type]
  apply Finset.sum_congr rfl
  intro r _hr
  rw [show (∑ b : Bool, signedUse use cap i a (r, b)) =
      signedUse use cap i a (r, false) +
        signedUse use cap i a (r, true) by simp]
  exact signedUse_pair_sum use cap i a r

/-- The row load of the complementary copy is the total cap minus the
original row load. -/
theorem rowLoad_signedUse_true
    (use : Source → State → Row → ℝ) (cap : Source → Row → ℝ)
    (choice : Source → State) (r : Row) :
    rowLoad (signedUse use cap) (r, true) choice =
      (∑ i : Source, cap i r) - rowLoad use r choice := by
  unfold rowLoad signedUse
  rw [Finset.sum_sub_distrib]

/-- The mean of the complementary copy is the total cap minus the original
mean. -/
theorem rowMean_signedUse_true
    (prob : Source → State → ℝ)
    (use : Source → State → Row → ℝ) (cap : Source → Row → ℝ)
    (hprobSum : ∀ i, ∑ a, prob i a = 1) (r : Row) :
    rowMean prob (signedUse use cap) (r, true) =
      (∑ i : Source, cap i r) - rowMean prob use r := by
  unfold rowMean signedUse
  calc
    (∑ i : Source, ∑ a : State,
        prob i a * (cap i r - use i a r)) =
        ∑ i : Source,
          (cap i r * (∑ a : State, prob i a) -
            ∑ a : State, prob i a * use i a r) := by
      apply Finset.sum_congr rfl
      intro i _hi
      rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
      apply Finset.sum_congr rfl
      intro a _ha
      ring
    _ = (∑ i : Source, cap i r) -
          ∑ i : Source, ∑ a : State, prob i a * use i a r := by
      simp_rw [hprobSum]
      simp only [mul_one, Finset.sum_sub_distrib]
    _ = _ := rfl

@[simp] theorem rowLoad_signedUse_false
    (use : Source → State → Row → ℝ) (cap : Source → Row → ℝ)
    (choice : Source → State) (r : Row) :
    rowLoad (signedUse use cap) (r, false) choice = rowLoad use r choice := by
  rfl

@[simp] theorem rowMean_signedUse_false
    (prob : Source → State → ℝ)
    (use : Source → State → Row → ℝ) (cap : Source → Row → ℝ)
    (r : Row) :
    rowMean prob (signedUse use cap) (r, false) = rowMean prob use r := by
  rfl

/-- Simultaneously keep every statistic within one mass-sensitive packing
deviation of its own mean.  The hypotheses `hmeanUpper` and `hmeanLower`
bound the expected upper statistic and the expected complementary statistic,
respectively.  In the Kempe application both are of the same order.

The conclusion is deterministic and also preserves positive categorical
support at every source. -/
theorem exists_supported_choice_abs_rowLoad_sub_mean_lt_deviation
    (R C : ℝ) (hR : 0 < R) (hC : 0 ≤ C) (hC1 : 1 ≤ C)
    (K : ℕ) (hK : 0 < K) (hRK : R ≤ K)
    (prob : Source → State → ℝ) (dummyProb : State → ℝ)
    (use : Source → State → Row → ℝ) (cap : Source → Row → ℝ)
    (hprob0 : ∀ i a, 0 ≤ prob i a)
    (hprobSum : ∀ i, ∑ a, prob i a = 1)
    (hdummy0 : ∀ a, 0 ≤ dummyProb a)
    (hdummySum : ∑ a, dummyProb a = 1)
    (huse0 : ∀ i a r, 0 ≤ use i a r)
    (huseCap : ∀ i a r, use i a r ≤ cap i r)
    (hcap1 : ∀ i r, cap i r ≤ 1)
    (hmeanUpper : ∀ r, rowMean prob use r ≤ R)
    (hmeanLower : ∀ r,
      (∑ i : Source, cap i r) - rowMean prob use r ≤ R)
    (hcolumn : ∀ i, ∑ r : Row, cap i r ≤ C) :
    ∃ choice : Source → State,
      (∀ i, 0 < prob i (choice i)) ∧
      ∀ r,
        |rowLoad use r choice - rowMean prob use r| <
          packingDeviation R C := by
  let signed : Source → State → (Row × Bool) → ℝ := signedUse use cap
  have hsigned0 : ∀ i a sr, 0 ≤ signed i a sr := by
    intro i a sr
    rcases sr with ⟨r, b⟩
    cases b
    · exact huse0 i a r
    · exact sub_nonneg.mpr (huseCap i a r)
  have hsigned1 : ∀ i a sr, signed i a sr ≤ 1 := by
    intro i a sr
    rcases sr with ⟨r, b⟩
    cases b
    · exact (huseCap i a r).trans (hcap1 i r)
    · simp only [signed, signedUse]
      have := huse0 i a r
      linarith [hcap1 i r]
  have hmean : ∀ sr, rowMean prob signed sr ≤ R := by
    intro sr
    rcases sr with ⟨r, b⟩
    cases b
    · simpa [signed] using hmeanUpper r
    · rw [rowMean_signedUse_true prob use cap hprobSum r]
      exact hmeanLower r
  have hsignedColumn : ∀ i a, ∑ sr, signed i a sr ≤ C := by
    intro i a
    rw [show (∑ sr, signed i a sr) = ∑ r, cap i r by
      exact sum_signedUse_eq_sum_cap use cap i a]
    exact hcolumn i
  obtain ⟨choice, hsupport, hload⟩ :=
    exists_supported_choice_rowLoad_lt_rowMean_add_deviation
      R C hR hC hC1 K hK hRK prob dummyProb signed
      hprob0 hprobSum hdummy0 hdummySum hsigned0 hsigned1 hmean
      hsignedColumn
  refine ⟨choice, hsupport, ?_⟩
  intro r
  have hu := hload (r, false)
  have hl := hload (r, true)
  rw [show rowLoad signed (r, false) choice = rowLoad use r choice by rfl,
    show rowMean prob signed (r, false) = rowMean prob use r by rfl] at hu
  rw [show rowLoad signed (r, true) choice =
      (∑ i : Source, cap i r) - rowLoad use r choice by
        exact rowLoad_signedUse_true use cap choice r,
    show rowMean prob signed (r, true) =
      (∑ i : Source, cap i r) - rowMean prob use r by
        exact rowMean_signedUse_true prob use cap hprobSum r] at hl
  rw [abs_lt]
  constructor <;> linarith

/-- Rescaled form for summands bounded by an arbitrary positive `B`.
The mean and column parameters are divided by `B` before applying partial
resampling, and the final deviation is multiplied back by `B`.  This is the
literal normalization used for the `z`, `d`, and `Z` Kempe statistics. -/
theorem exists_supported_choice_abs_rowLoad_sub_mean_lt_scaledDeviation
    (M D B : ℝ) (hM : 0 < M) (hD : 0 ≤ D) (hB : 0 < B)
    (hDB1 : 1 ≤ D / B)
    (K : ℕ) (hK : 0 < K) (hMK : M / B ≤ K)
    (prob : Source → State → ℝ) (dummyProb : State → ℝ)
    (use : Source → State → Row → ℝ) (cap : Source → Row → ℝ)
    (hprob0 : ∀ i a, 0 ≤ prob i a)
    (hprobSum : ∀ i, ∑ a, prob i a = 1)
    (hdummy0 : ∀ a, 0 ≤ dummyProb a)
    (hdummySum : ∑ a, dummyProb a = 1)
    (huse0 : ∀ i a r, 0 ≤ use i a r)
    (huseCap : ∀ i a r, use i a r ≤ cap i r)
    (hcapB : ∀ i r, cap i r ≤ B)
    (hmeanUpper : ∀ r, rowMean prob use r ≤ M)
    (hmeanLower : ∀ r,
      (∑ i : Source, cap i r) - rowMean prob use r ≤ M)
    (hcolumn : ∀ i, ∑ r : Row, cap i r ≤ D) :
    ∃ choice : Source → State,
      (∀ i, 0 < prob i (choice i)) ∧
      ∀ r,
        |rowLoad use r choice - rowMean prob use r| <
          B * packingDeviation (M / B) (D / B) := by
  let scaledUse : Source → State → Row → ℝ :=
    fun i a r ↦ use i a r / B
  let scaledCap : Source → Row → ℝ :=
    fun i r ↦ cap i r / B
  have hscaledUse0 : ∀ i a r, 0 ≤ scaledUse i a r := by
    intro i a r
    exact div_nonneg (huse0 i a r) hB.le
  have hscaledUseCap : ∀ i a r, scaledUse i a r ≤ scaledCap i r := by
    intro i a r
    exact div_le_div_of_nonneg_right (huseCap i a r) hB.le
  have hscaledCap1 : ∀ i r, scaledCap i r ≤ 1 := by
    intro i r
    exact (div_le_one hB).2 (hcapB i r)
  have hmeanScaled (r : Row) :
      rowMean prob scaledUse r = rowMean prob use r / B := by
    unfold rowMean scaledUse
    simp_rw [← mul_div_assoc]
    simp_rw [← Finset.sum_div]
  have hcapSumScaled (r : Row) :
      (∑ i : Source, scaledCap i r) =
        (∑ i : Source, cap i r) / B := by
    unfold scaledCap
    rw [← Finset.sum_div]
  have hrowLoadScaled (choice : Source → State) (r : Row) :
      rowLoad scaledUse r choice = rowLoad use r choice / B := by
    unfold rowLoad scaledUse
    rw [← Finset.sum_div]
  have hscaledMeanUpper : ∀ r, rowMean prob scaledUse r ≤ M / B := by
    intro r
    rw [hmeanScaled]
    exact div_le_div_of_nonneg_right (hmeanUpper r) hB.le
  have hscaledMeanLower : ∀ r,
      (∑ i : Source, scaledCap i r) - rowMean prob scaledUse r ≤ M / B := by
    intro r
    rw [hcapSumScaled, hmeanScaled]
    rw [← sub_div]
    exact div_le_div_of_nonneg_right (hmeanLower r) hB.le
  have hscaledColumn : ∀ i, ∑ r : Row, scaledCap i r ≤ D / B := by
    intro i
    unfold scaledCap
    rw [← Finset.sum_div]
    exact div_le_div_of_nonneg_right (hcolumn i) hB.le
  obtain ⟨choice, hsupport, hdeviation⟩ :=
    exists_supported_choice_abs_rowLoad_sub_mean_lt_deviation
      (M / B) (D / B) (div_pos hM hB) (div_nonneg hD hB.le) hDB1
      K hK hMK prob dummyProb scaledUse scaledCap
      hprob0 hprobSum hdummy0 hdummySum hscaledUse0 hscaledUseCap
      hscaledCap1 hscaledMeanUpper hscaledMeanLower hscaledColumn
  refine ⟨choice, hsupport, ?_⟩
  intro r
  have hr := hdeviation r
  rw [hrowLoadScaled, hmeanScaled, ← sub_div, abs_div,
    abs_of_pos hB] at hr
  have := (div_lt_iff₀ hB).mp hr
  simpa [mul_comm] using this

/-! ## The two asymptotic scales in the moment argument -/

/-- If an unscaled summand is `O(1/n)`, while the scaled row and column
parameters are `O(n)` and `O(n²)`, its unscaled packing error tends to zero.
This is the first-moment (`z`) scale. -/
theorem eventually_mul_packingDeviation_le_of_inv_linear
    {B0 A C0 : ℝ} (hB0 : 0 < B0) (hA : 0 ≤ A) (hC0 : 0 ≤ C0) :
    ∀ eps : ℝ, 0 < eps → ∃ N : ℕ, ∀ n : ℕ, N ≤ n → 0 < n →
      ∀ B R C : ℝ, 0 ≤ B → 0 ≤ R → 0 ≤ C →
        B ≤ B0 / n → R ≤ A * n → C ≤ C0 * (n : ℝ) ^ 2 →
          B * packingDeviation R C ≤ eps := by
  intro eps heps
  obtain ⟨N, hN⟩ :=
    FinitePartialResamplingNumerics.packingDeviation_sublinear_of_linear_row_quadratic_column
        hA hC0 (eps / B0) (div_pos heps hB0)
  refine ⟨N, ?_⟩
  intro n hn hnpos B R C hB hR hC hBinv hRlin hCquad
  have hdev := hN n hn R C hR hC hRlin hCquad
  have hnR : (0 : ℝ) < n := by exact_mod_cast hnpos
  have hBn : B * n ≤ B0 := by
    apply (le_div_iff₀ hnR).mp
    simpa [mul_comm] using hBinv
  calc
    B * packingDeviation R C ≤ B * ((eps / B0) * n) :=
      mul_le_mul_of_nonneg_left hdev hB
    _ = (eps / B0) * (B * n) := by ring
    _ ≤ (eps / B0) * B0 :=
      mul_le_mul_of_nonneg_left hBn (div_nonneg heps.le hB0.le)
    _ = eps := by field_simp

/-- If an unscaled summand is `O(1/n²)` under the same scaled row/column
bounds, its unscaled packing error is `o(1/n)`.  This is the diagonal and
pair-moment (`d,Z`) scale. -/
theorem eventually_mul_packingDeviation_le_inv_of_inv_quadratic
    {B0 A C0 : ℝ} (hB0 : 0 < B0) (hA : 0 ≤ A) (hC0 : 0 ≤ C0) :
    ∀ eps : ℝ, 0 < eps → ∃ N : ℕ, ∀ n : ℕ, N ≤ n → 0 < n →
      ∀ B R C : ℝ, 0 ≤ B → 0 ≤ R → 0 ≤ C →
        B ≤ B0 / (n : ℝ) ^ 2 →
        R ≤ A * n → C ≤ C0 * (n : ℝ) ^ 2 →
          B * packingDeviation R C ≤ eps / n := by
  intro eps heps
  obtain ⟨N, hN⟩ :=
    FinitePartialResamplingNumerics.packingDeviation_sublinear_of_linear_row_quadratic_column
        hA hC0 (eps / B0) (div_pos heps hB0)
  refine ⟨N, ?_⟩
  intro n hn hnpos B R C hB hR hC hBquad hRlin hCquad
  have hdev := hN n hn R C hR hC hRlin hCquad
  have hnR : (0 : ℝ) < n := by exact_mod_cast hnpos
  have hBnSq : B * (n : ℝ) ^ 2 ≤ B0 := by
    apply (le_div_iff₀ (sq_pos_of_pos hnR)).mp
    simpa [mul_comm] using hBquad
  have hBn : B * n ≤ B0 / n := by
    apply (le_div_iff₀ hnR).2
    calc
      B * (n : ℝ) * n = B * (n : ℝ) ^ 2 := by ring
      _ ≤ B0 := hBnSq
  calc
    B * packingDeviation R C ≤ B * ((eps / B0) * n) :=
      mul_le_mul_of_nonneg_left hdev hB
    _ = (eps / B0) * (B * n) := by ring
    _ ≤ (eps / B0) * (B0 / n) :=
      mul_le_mul_of_nonneg_left hBn (div_nonneg heps.le hB0.le)
    _ = eps / n := by field_simp

end

end WeightedEdgeColoring.WeightedMomentTwoSidedSelection
