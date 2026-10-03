import WeightedEdgeColoring.FinitePartialResamplingPackingOffset
import WeightedEdgeColoring.FinitePartialResamplingNumericsBounds

/-!
# Packing selection relative to each row's own mean

The offset selector is most convenient through this corollary.  If every
row mean is at most a common scale `R`, deterministic dummy sources fill the
gap from that mean to `R`.  Removing the dummies leaves a supported choice
whose load on every row is smaller than its own mean plus the common packing
deviation.
-/

namespace WeightedEdgeColoring.FiniteCategoricalSelection

open scoped BigOperators
open WeightedEdgeColoring.FinitePartialResamplingNumerics

noncomputable section

variable {Source State Row : Type*}
variable [Fintype Source] [DecidableEq Source]
variable [Fintype State] [DecidableEq State]
variable [Fintype Row] [DecidableEq Row]

theorem exists_supported_choice_rowLoad_lt_rowMean_add_deviation
    (R C : ℝ) (hR : 0 < R) (hC : 0 ≤ C) (hC1 : 1 ≤ C)
    (K : ℕ) (hK : 0 < K) (hRK : R ≤ K)
    (prob : Source → State → ℝ) (dummyProb : State → ℝ)
    (use : Source → State → Row → ℝ)
    (hprob0 : ∀ i a, 0 ≤ prob i a)
    (hprobSum : ∀ i, ∑ a, prob i a = 1)
    (hdummy0 : ∀ a, 0 ≤ dummyProb a)
    (hdummySum : ∑ a, dummyProb a = 1)
    (huse0 : ∀ i a r, 0 ≤ use i a r)
    (huse1 : ∀ i a r, use i a r ≤ 1)
    (hmean : ∀ r, rowMean prob use r ≤ R)
    (hcolumn : ∀ i a, ∑ r, use i a r ≤ C) :
    ∃ choice : Source → State,
      (∀ i, 0 < prob i (choice i)) ∧
      ∀ r, rowLoad use r choice <
        rowMean prob use r + packingDeviation R C := by
  let offset : Row → ℝ := fun r ↦ R - rowMean prob use r
  have hmean0 : ∀ r, 0 ≤ rowMean prob use r := by
    intro r
    unfold rowMean
    apply Finset.sum_nonneg
    intro i _hi
    apply Finset.sum_nonneg
    intro a _ha
    exact mul_nonneg (hprob0 i a) (huse0 i a r)
  have hoffset0 : ∀ r, 0 ≤ offset r := by
    intro r
    exact sub_nonneg.mpr (hmean r)
  have hoffsetK : ∀ r, offset r ≤ K := by
    intro r
    calc
      offset r = R - rowMean prob use r := rfl
      _ ≤ R := sub_le_self R (hmean0 r)
      _ ≤ K := hRK
  have hoffsetMean : ∀ r, offset r + rowMean prob use r ≤ R := by
    intro r
    dsimp [offset]
    linarith
  obtain ⟨choice, hchoice, hload⟩ :=
    exists_supported_choice_offset_add_rowLoad_lt_packingThreshold
      R C hR hC hC1 K hK prob dummyProb use offset
      hprob0 hprobSum hdummy0 hdummySum huse0 huse1
      hoffset0 hoffsetK hoffsetMean hcolumn
  refine ⟨choice, hchoice, ?_⟩
  intro r
  have hthreshold :=
    packingThreshold_le_base_add_deviation hR hC
  have htotal : offset r + rowLoad use r choice <
      R + packingDeviation R C :=
    (hload r).trans_le hthreshold
  dsimp [offset] at htotal
  linarith

end

end WeightedEdgeColoring.FiniteCategoricalSelection
