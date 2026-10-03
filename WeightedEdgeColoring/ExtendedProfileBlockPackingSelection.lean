import WeightedEdgeColoring.ExtendedProfileWordPadding
import WeightedEdgeColoring.FinitePartialResamplingPackingSelection
import WeightedEdgeColoring.FinitePartialResamplingNumericsBounds

/-!
# Packing selection with fixed colour blocks

For the quadratic clipping estimate, the colours are split into blocks of a
fixed size `k`.  One categorical source is a pair `(vertex, block)`, and its
state is a complete `Fin k` word of extended-profile atoms.  The common
state space has size `M^k`, where `M = extendedProfileStateBound`; for fixed
accuracy parameters this is independent of the number of colours.

This file only constructs and selects supported block words.  Capacity,
first-moment, and block-variance rows can all be supplied through the
arbitrary additive `use` argument.
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

/-- One source-independent code for a `Fin k` block of extended states. -/
abbrev ExtendedProfilePackedBlockState (k : ℕ) (β q r : ℝ) :=
  FiniteDependentWordPadding.PackedWordState
    (Color := Fin k) (extendedProfileStateBound β q r)

/-- Block and within-block coordinates of a colour in an exactly padded
`B * k` palette. -/
def extendedProfileColorBlock (c : Fin (B * k)) : Fin B :=
  (finProdFinEquiv.symm c).1

def extendedProfileColorPosition (c : Fin (B * k)) : Fin k :=
  (finProdFinEquiv.symm c).2

@[simp] theorem extendedProfileColorBlock_mk (b : Fin B) (j : Fin k) :
    extendedProfileColorBlock (finProdFinEquiv (b, j)) = b := by
  simp [extendedProfileColorBlock]

@[simp] theorem extendedProfileColorPosition_mk (b : Fin B) (j : Fin k) :
    extendedProfileColorPosition (finProdFinEquiv (b, j)) = j := by
  simp [extendedProfileColorPosition]

/-- Flatten selected block words back into an ordinary colour word. -/
def flattenExtendedProfileBlocks
    (selected : ∀ v (b : Fin B),
      Fin k → G.ExtendedProfileState R0 v) :
    ∀ v, Fin (B * k) → G.ExtendedProfileState R0 v :=
  fun v c ↦ selected v (extendedProfileColorBlock c)
    (extendedProfileColorPosition c)

@[simp] theorem flattenExtendedProfileBlocks_mk
    (selected : ∀ v (b : Fin B),
      Fin k → G.ExtendedProfileState R0 v)
    (v : G.V) (b : Fin B) (j : Fin k) :
    G.flattenExtendedProfileBlocks R0 selected v (finProdFinEquiv (b, j)) =
      selected v b j := by
  simp [flattenExtendedProfileBlocks]

/-- Decode a common block code at a specified vertex. -/
def decodeExtendedProfileBlock (v : G.V)
    (a : ExtendedProfilePackedBlockState k β q r) :
    Fin k → G.ExtendedProfileState R0 v :=
  FiniteDependentWordPadding.decodePackedWord
    (fun v ↦ G.ExtendedProfileState R0 v) (Color := Fin k)
    (G.extendedProfileStateEncoding R0)
    (G.inactiveExtendedProfileState R0) v a

@[simp] theorem decode_encodeExtendedProfileBlock (v : G.V)
    (word : Fin k → G.ExtendedProfileState R0 v) :
    G.decodeExtendedProfileBlock R0 v
        (FiniteDependentWordPadding.encodePackedWord
          (fun v ↦ G.ExtendedProfileState R0 v) (Color := Fin k)
          (G.extendedProfileStateEncoding R0) v word) = word := by
  exact FiniteDependentWordPadding.decodePackedWord_encode
    (fun v ↦ G.ExtendedProfileState R0 v) (Color := Fin k)
    (G.extendedProfileStateEncoding R0)
    (G.inactiveExtendedProfileState R0) v word

/-- Product mass of one genuine block word. -/
def extendedProfileBlockMass (omega : ℝ) (v : G.V)
    (word : Fin k → G.ExtendedProfileState R0 v) : ℝ :=
  ∏ j, G.smoothedExtendedProfileProbability R0 omega v (word j)

/-- The product block law, padded by zero into the common block state. -/
def paddedExtendedProfileBlockProbability (omega : ℝ) (v : G.V)
    (a : ExtendedProfilePackedBlockState k β q r) : ℝ :=
  FiniteDependentWordPadding.paddedWordProbability
    (fun v ↦ G.ExtendedProfileState R0 v)
    (G.extendedProfileStateEncoding R0)
    (fun v z ↦ G.smoothedExtendedProfileProbability R0 omega v z) v a

theorem sum_paddedExtendedProfileBlockProbability
    (omega : ℝ) (v : G.V) :
    ∑ a, G.paddedExtendedProfileBlockProbability R0 omega v a = 1 := by
  exact FiniteDependentWordPadding.sum_paddedWordProbability
    (fun v ↦ G.ExtendedProfileState R0 v)
    (G.extendedProfileStateEncoding R0)
    (fun v z ↦ G.smoothedExtendedProfileProbability R0 omega v z)
    (G.sum_smoothedExtendedProfileProbability R0 omega) v

theorem paddedExtendedProfileBlockProbability_nonneg
    (hs : 0 ≤ s) (hq : 0 ≤ q) (hr0 : 0 ≤ r)
    (hleft : 0 ≤ 1 - s * (1 + q + r))
    (homega0 : 0 < omega) (homega1 : omega ≤ 1)
    (v : G.V) (a : ExtendedProfilePackedBlockState k β q r) :
    0 ≤ G.paddedExtendedProfileBlockProbability R0 omega v a := by
  apply FiniteDependentWordPadding.paddedWordProbability_nonneg
    (fun v ↦ G.ExtendedProfileState R0 v)
    (G.extendedProfileStateEncoding R0)
    (fun v z ↦ G.smoothedExtendedProfileProbability R0 omega v z)
  intro x z
  exact (G.smoothedExtendedProfileProbability_pos R0 hs hq hr0 hleft
    homega0 homega1 x z).le

/-- Positive padded block mass decodes to a genuine positive-mass word. -/
theorem exists_extendedProfileBlock_of_padded_pos
    (hs : 0 ≤ s) (hq : 0 ≤ q) (hr0 : 0 ≤ r)
    (hleft : 0 ≤ 1 - s * (1 + q + r))
    (homega0 : 0 < omega) (homega1 : omega ≤ 1)
    (v : G.V) (a : ExtendedProfilePackedBlockState k β q r)
    (ha : 0 < G.paddedExtendedProfileBlockProbability R0 omega v a) :
    ∃ word : Fin k → G.ExtendedProfileState R0 v,
      FiniteDependentWordPadding.encodePackedWord
          (fun v ↦ G.ExtendedProfileState R0 v) (Color := Fin k)
          (G.extendedProfileStateEncoding R0) v word = a ∧
        0 < G.extendedProfileBlockMass R0 omega v word := by
  simpa [extendedProfileBlockMass] using
    (FiniteDependentWordPadding.exists_word_of_paddedWordProbability_pos
      (fun v ↦ G.ExtendedProfileState R0 v)
      (G.extendedProfileStateEncoding R0)
      (fun v z ↦ G.smoothedExtendedProfileProbability R0 omega v z)
      (fun x z ↦ (G.smoothedExtendedProfileProbability_pos R0 hs hq hr0
        hleft homega0 homega1 x z).le) v a ha)

variable {Row : Type w} [Fintype Row] [DecidableEq Row]

/-- Supported packing selection of one genuine block word for every
vertex--block source. -/
theorem exists_extendedProfileBlock_rowLoad_lt_packing
    (omega : ℝ)
    (hs : 0 ≤ s) (hq : 0 ≤ q) (hr0 : 0 ≤ r)
    (hleft : 0 ≤ 1 - s * (1 + q + r))
    (homega0 : 0 < omega) (homega1 : omega ≤ 1)
    (use : (G.V × Fin B) → ExtendedProfilePackedBlockState k β q r →
      Row → ℝ)
    (meanBound columnBound : ℝ)
    (hmeanBound : 0 < meanBound) (hcolumnBound : 0 ≤ columnBound)
    (huse0 : ∀ src a row, 0 ≤ use src a row)
    (huse1 : ∀ src a row, use src a row ≤ 1)
    (hmean : ∀ row,
      FiniteCategoricalSelection.rowMean
          (fun src a ↦
            G.paddedExtendedProfileBlockProbability R0 omega src.1 a)
          use row ≤ meanBound)
    (hcolumn : ∀ src a, ∑ row, use src a row ≤ columnBound) :
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
          meanBound +
            FinitePartialResamplingNumerics.packingDeviation
              meanBound columnBound := by
  let prob : (G.V × Fin B) → ExtendedProfilePackedBlockState k β q r → ℝ :=
    fun src a ↦ G.paddedExtendedProfileBlockProbability R0 omega src.1 a
  obtain ⟨choice, hchoicePos, hchoiceLoad⟩ :=
    FiniteCategoricalSelection.exists_supported_choice_rowLoad_lt_packingThreshold
      meanBound columnBound hmeanBound hcolumnBound prob use
      (fun src a ↦ G.paddedExtendedProfileBlockProbability_nonneg R0
        hs hq hr0 hleft homega0 homega1 src.1 a)
      (fun src ↦ G.sum_paddedExtendedProfileBlockProbability R0 omega src.1)
      huse0 huse1 hmean hcolumn
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
    have hthreshold :=
      FinitePartialResamplingNumerics.packingThreshold_le_base_add_deviation
        hmeanBound hcolumnBound
    calc
      (∑ src : G.V × Fin B,
          use src
            (FiniteDependentWordPadding.encodePackedWord
              (fun v ↦ G.ExtendedProfileState R0 v) (Color := Fin k)
              (G.extendedProfileStateEncoding R0) src.1
              (selected src.1 src.2)) row) =
          FiniteCategoricalSelection.rowLoad use row choice := by
        simp only [FiniteCategoricalSelection.rowLoad, hcode]
      _ < FinitePartialResamplingNumerics.packingThreshold
          meanBound columnBound := hload
      _ ≤ meanBound +
          FinitePartialResamplingNumerics.packingDeviation
            meanBound columnBound := hthreshold

end WeightedSimpleGraph

end

end WeightedEdgeColoring
