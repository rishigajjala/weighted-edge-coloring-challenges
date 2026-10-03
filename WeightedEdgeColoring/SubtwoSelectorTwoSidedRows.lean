import WeightedEdgeColoring.FinitePartialResamplingPackingMeanSelection

/-!
# Two-sided categorical rows

An upper packing row can also certify a lower row bound.  For a state-
independent source envelope `cap`, append the complementary nonnegative
use `cap - use`.  Its selected upper bound reverses to a lower bound on
the original selected load with exactly the same deviation.  In the mixed
graph selector the envelope must be sparse or weight-scaled so that adding
these rows does not inflate the common deviation.
-/

namespace WeightedEdgeColoring.FiniteCategoricalSelection

open scoped BigOperators

variable {Source State Row : Type*}
variable [Fintype Source] [Fintype State]

/-- The original and complementary uses share a row index. -/
def twoSidedUse
    (cap : Source → Row → ℝ)
    (use : Source → State → Row → ℝ) :
    Source → State → Row × Bool → ℝ :=
  fun i a rb ↦ if rb.2 then cap i rb.1 - use i a rb.1 else use i a rb.1

theorem complement_nonneg
    (cap : Source → Row → ℝ)
    (use : Source → State → Row → ℝ)
    (hcap : ∀ i a r, use i a r ≤ cap i r) :
    ∀ i a r, 0 ≤ cap i r - use i a r := by
  intro i a r
  exact sub_nonneg.mpr (hcap i a r)

theorem complement_le_one
    (cap : Source → Row → ℝ)
    (use : Source → State → Row → ℝ)
    (hcap1 : ∀ i r, cap i r ≤ 1)
    (huse0 : ∀ i a r, 0 ≤ use i a r) :
    ∀ i a r, cap i r - use i a r ≤ 1 := by
  intro i a r
  exact (sub_le_self _ (huse0 i a r)).trans (hcap1 i r)

theorem rowLoad_complement
    (cap : Source → Row → ℝ)
    (use : Source → State → Row → ℝ)
    (r : Row) (choice : Source → State) :
    rowLoad (fun i a j ↦ cap i j - use i a j) r choice =
      (∑ i, cap i r) - rowLoad use r choice := by
  simp [rowLoad, Finset.sum_sub_distrib]

theorem rowMean_complement
    (prob : Source → State → ℝ)
    (hprobSum : ∀ i, ∑ a, prob i a = 1)
    (cap : Source → Row → ℝ)
    (use : Source → State → Row → ℝ)
    (r : Row) :
    rowMean prob (fun i a j ↦ cap i j - use i a j) r =
      (∑ i, cap i r) - rowMean prob use r := by
  simp only [rowMean, mul_sub, Finset.sum_sub_distrib]
  congr 1
  apply Finset.sum_congr rfl
  intro i _
  rw [← Finset.sum_mul, hprobSum i, one_mul]

/-- The complement row yields lower selected mass, including a strict
margin when the packing selector has a strict row bound. -/
theorem rowLoad_gt_mean_sub_of_complement
    (prob : Source → State → ℝ)
    (hprobSum : ∀ i, ∑ a, prob i a = 1)
    (cap : Source → Row → ℝ)
    (use : Source → State → Row → ℝ)
    (r : Row) (choice : Source → State) (deviation : ℝ)
    (hupper :
      rowLoad (fun i a j ↦ cap i j - use i a j) r choice <
        rowMean prob (fun i a j ↦ cap i j - use i a j) r + deviation) :
    rowMean prob use r - deviation < rowLoad use r choice := by
  rw [rowLoad_complement cap use,
    rowMean_complement prob hprobSum cap use] at hupper
  linarith

/-- The packing selector can enforce upper and lower loads at once.  The
model-specific work is to supply a state-independent envelope with a small
two-sided column sum; the conclusion itself loses only one deviation. -/
theorem exists_supported_choice_twoSided
    [DecidableEq Source] [DecidableEq State]
    [Fintype Row] [DecidableEq Row]
    (R C : ℝ) (hR : 0 < R) (hC : 0 ≤ C) (hC1 : 1 ≤ C)
    (K : ℕ) (hK : 0 < K) (hRK : R ≤ K)
    (prob : Source → State → ℝ) (dummyProb : State → ℝ)
    (cap : Source → Row → ℝ)
    (use : Source → State → Row → ℝ)
    (hprob0 : ∀ i a, 0 ≤ prob i a)
    (hprobSum : ∀ i, ∑ a, prob i a = 1)
    (hdummy0 : ∀ a, 0 ≤ dummyProb a)
    (hdummySum : ∑ a, dummyProb a = 1)
    (huse0 : ∀ i a r, 0 ≤ use i a r)
    (huseCap : ∀ i a r, use i a r ≤ cap i r)
    (hcap1 : ∀ i r, cap i r ≤ 1)
    (hmean : ∀ rb, rowMean prob (twoSidedUse cap use) rb ≤ R)
    (hcolumn : ∀ i a, ∑ rb, twoSidedUse cap use i a rb ≤ C) :
    ∃ choice : Source → State,
      (∀ i, 0 < prob i (choice i)) ∧
      ∀ r,
        rowLoad use r choice <
          rowMean prob use r +
            WeightedEdgeColoring.FinitePartialResamplingNumerics.packingDeviation R C ∧
        rowMean prob use r -
            WeightedEdgeColoring.FinitePartialResamplingNumerics.packingDeviation R C <
          rowLoad use r choice := by
  have htwo0 : ∀ i a rb, 0 ≤ twoSidedUse cap use i a rb := by
    intro i a ⟨r, b⟩
    cases b <;> simp [twoSidedUse, huse0, complement_nonneg cap use huseCap]
  have htwo1 : ∀ i a rb, twoSidedUse cap use i a rb ≤ 1 := by
    intro i a ⟨r, b⟩
    cases b
    · simpa [twoSidedUse] using
        (huseCap i a r).trans (hcap1 i r)
    · simpa [twoSidedUse] using
        (complement_le_one cap use hcap1 huse0 i a r)
  obtain ⟨choice, hpositive, hrows⟩ :=
    exists_supported_choice_rowLoad_lt_rowMean_add_deviation
      R C hR hC hC1 K hK hRK prob dummyProb (twoSidedUse cap use)
      hprob0 hprobSum hdummy0 hdummySum htwo0 htwo1 hmean hcolumn
  refine ⟨choice, hpositive, ?_⟩
  intro r
  have hupper := hrows (r, false)
  have hlower := hrows (r, true)
  constructor
  · simpa [twoSidedUse] using hupper
  · apply rowLoad_gt_mean_sub_of_complement prob hprobSum cap use r choice
      (WeightedEdgeColoring.FinitePartialResamplingNumerics.packingDeviation R C)
    simpa [twoSidedUse] using hlower

end WeightedEdgeColoring.FiniteCategoricalSelection
