import WeightedEdgeColoring.ExtendedProfileBlockPackingSelection
import WeightedEdgeColoring.FinitePartialResamplingPackingMeanSelection

/-!
# Mean-relative packing selection for profile blocks

This is the support-preserving block-word wrapper around the generic
mean-relative categorical selector.  It is useful when several kinds of
rows have different expectations: every selected row is compared with its
own mean, while a single pair of bounds `R,C` controls the common packing
deviation.
-/

namespace WeightedEdgeColoring

open scoped BigOperators

noncomputable section

namespace WeightedSimpleGraph

universe u w

variable (G : WeightedSimpleGraph.{u})
variable {B k : ℕ}
variable {s β q r : ℝ} {hβ : 0 < β} {hr : 0 < r}
variable (R0 : ∀ v, G.BoundedProfileRealization
  (fun _e : G.StarEdge v ↦ (1 : ℝ) / ((B * k : ℕ) : ℝ))
    s β q r hβ hr)

variable {Row : Type w} [Fintype Row] [DecidableEq Row]

/-- Select genuine supported block words while keeping every additive row
within the common packing deviation of that row's own expectation. -/
theorem exists_extendedProfileBlock_rowLoad_lt_rowMean_add_deviation
    (omega : ℝ)
    (hs : 0 ≤ s) (hq : 0 ≤ q) (hr0 : 0 ≤ r)
    (hleft : 0 ≤ 1 - s * (1 + q + r))
    (homega0 : 0 < omega) (homega1 : omega ≤ 1)
    (use : (G.V × Fin B) → ExtendedProfilePackedBlockState k β q r →
      Row → ℝ)
    (R C : ℝ) (hR : 0 < R) (hC : 0 ≤ C) (hC1 : 1 ≤ C)
    (K : ℕ) (hK : 0 < K) (hRK : R ≤ K)
    (dummyProb : ExtendedProfilePackedBlockState k β q r → ℝ)
    (hdummy0 : ∀ a, 0 ≤ dummyProb a)
    (hdummySum : ∑ a, dummyProb a = 1)
    (huse0 : ∀ src a row, 0 ≤ use src a row)
    (huse1 : ∀ src a row, use src a row ≤ 1)
    (hmean : ∀ row,
      FiniteCategoricalSelection.rowMean
          (fun src a ↦
            G.paddedExtendedProfileBlockProbability R0 omega src.1 a)
          use row ≤ R)
    (hcolumn : ∀ src a, ∑ row, use src a row ≤ C) :
    ∃ selected : ∀ v (b : Fin B),
        Fin k → G.ExtendedProfileState R0 v,
      (∀ v b,
        0 < G.extendedProfileBlockMass R0 omega v (selected v b)) ∧
      ∀ row,
        (∑ src : G.V × Fin B,
          use src
            (FiniteDependentWordPadding.encodePackedWord
              (fun v ↦ G.ExtendedProfileState R0 v) (Color := Fin k)
              (G.extendedProfileStateEncoding R0) src.1
              (selected src.1 src.2)) row) <
          FiniteCategoricalSelection.rowMean
            (fun src a ↦
              G.paddedExtendedProfileBlockProbability R0 omega src.1 a)
            use row +
              FinitePartialResamplingNumerics.packingDeviation R C := by
  let prob : (G.V × Fin B) → ExtendedProfilePackedBlockState k β q r → ℝ :=
    fun src a ↦ G.paddedExtendedProfileBlockProbability R0 omega src.1 a
  obtain ⟨choice, hchoicePos, hchoiceLoad⟩ :=
    FiniteCategoricalSelection.exists_supported_choice_rowLoad_lt_rowMean_add_deviation
      R C hR hC hC1 K hK hRK prob dummyProb use
      (fun src a ↦ G.paddedExtendedProfileBlockProbability_nonneg R0
        hs hq hr0 hleft homega0 homega1 src.1 a)
      (fun src ↦ G.sum_paddedExtendedProfileBlockProbability R0 omega src.1)
      hdummy0 hdummySum huse0 huse1 hmean hcolumn
  have hdecode : ∀ src : G.V × Fin B,
      ∃ word : Fin k → G.ExtendedProfileState R0 src.1,
        FiniteDependentWordPadding.encodePackedWord
            (fun v ↦ G.ExtendedProfileState R0 v) (Color := Fin k)
            (G.extendedProfileStateEncoding R0) src.1 word = choice src ∧
          0 < G.extendedProfileBlockMass R0 omega src.1 word := by
    intro src
    exact G.exists_extendedProfileBlock_of_padded_pos R0 hs hq hr0 hleft
      homega0 homega1 src.1 (choice src) (hchoicePos src)
  let selected : ∀ v (b : Fin B),
      Fin k → G.ExtendedProfileState R0 v :=
    fun v b ↦ Classical.choose (hdecode (v, b))
  have hcode : ∀ src : G.V × Fin B,
      FiniteDependentWordPadding.encodePackedWord
          (fun v ↦ G.ExtendedProfileState R0 v) (Color := Fin k)
          (G.extendedProfileStateEncoding R0) src.1
          (selected src.1 src.2) = choice src := by
    intro src
    exact (Classical.choose_spec (hdecode src)).1
  refine ⟨selected, ?_, ?_⟩
  · intro v b
    exact (Classical.choose_spec (hdecode (v, b))).2
  · intro row
    have hload := hchoiceLoad row
    change (∑ src : G.V × Fin B,
      use src (choice src) row) <
        FiniteCategoricalSelection.rowMean prob use row +
          FinitePartialResamplingNumerics.packingDeviation R C at hload
    simpa [prob, hcode] using hload

end WeightedSimpleGraph

end

end WeightedEdgeColoring
