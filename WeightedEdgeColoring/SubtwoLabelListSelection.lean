import WeightedEdgeColoring.WeightedMomentTwoSidedSelection

/-!
# Add endpoint-label counts to a categorical list selection

The selector already accepts an arbitrary finite row family.  Append one
indicator row for each block and endpoint label.  Each source contributes to
at most the fixed number of label rows, so the column parameter grows by
only that number.  The two-sided selector then controls label counts along
with any existing profile or vertex-load rows.
-/

open scoped BigOperators

namespace WeightedEdgeColoring.Subtwo

variable {Source State Row Block Label : Type*}
  [Fintype Source] [DecidableEq Source]
  [Fintype State] [DecidableEq State]
  [Fintype Row] [DecidableEq Row]
  [Fintype Block] [DecidableEq Block]
  [Fintype Label] [DecidableEq Label]

/-- Original rows plus one color-count row for each block/label pair. -/
def labelAugmentedUse
    (baseUse : Source → State → Row → ℝ)
    (blockOf : Source → Block) (stateLabel : State → Label) :
    Source → State → (Row ⊕ (Block × Label)) → ℝ
  | src, state, Sum.inl row => baseUse src state row
  | src, state, Sum.inr (block, label) =>
      if blockOf src = block ∧ stateLabel state = label then 1 else 0

/-- A state-independent cap for each appended label row. -/
def labelAugmentedCap
    (baseCap : Source → Row → ℝ) (blockOf : Source → Block) :
    Source → (Row ⊕ (Block × Label)) → ℝ
  | src, Sum.inl row => baseCap src row
  | src, Sum.inr (block, _) => if blockOf src = block then 1 else 0

theorem labelAugmentedUse_nonneg
    (baseUse : Source → State → Row → ℝ)
    (hbase : ∀ src state row, 0 ≤ baseUse src state row)
    (blockOf : Source → Block) (stateLabel : State → Label) :
    ∀ src state row, 0 ≤ labelAugmentedUse baseUse blockOf stateLabel src state row := by
  intro src state row
  cases row with
  | inl row => exact hbase src state row
  | inr bl => simp [labelAugmentedUse]; split_ifs <;> norm_num

theorem labelAugmentedUse_le_cap
    (baseUse : Source → State → Row → ℝ)
    (baseCap : Source → Row → ℝ)
    (hbase : ∀ src state row, baseUse src state row ≤ baseCap src row)
    (blockOf : Source → Block) (stateLabel : State → Label) :
    ∀ src state row,
      labelAugmentedUse baseUse blockOf stateLabel src state row ≤
        labelAugmentedCap baseCap blockOf src row := by
  intro src state row
  cases row with
  | inl row => exact hbase src state row
  | inr bl =>
      by_cases hb : blockOf src = bl.1
      · simp [labelAugmentedUse, labelAugmentedCap, hb]
        split_ifs <;> norm_num
      · simp [labelAugmentedUse, labelAugmentedCap, hb]

theorem labelAugmentedCap_le_one
    (baseCap : Source → Row → ℝ)
    (hbase : ∀ src row, baseCap src row ≤ 1)
    (blockOf : Source → Block) :
    ∀ src (row : Row ⊕ (Block × Label)),
      labelAugmentedCap baseCap blockOf src row ≤ 1 := by
  intro src row
  cases row with
  | inl row => exact hbase src row
  | inr bl => simp [labelAugmentedCap]; split_ifs <;> norm_num

theorem labelAugmentedCap_column
    (baseCap : Source → Row → ℝ) (blockOf : Source → Block)
    (src : Source) :
    (∑ row : Row ⊕ (Block × Label),
        labelAugmentedCap baseCap blockOf src row) =
      (∑ row : Row, baseCap src row) + (Fintype.card Label : ℝ) := by
  rw [Fintype.sum_sum_type, Fintype.sum_prod_type]
  simp [labelAugmentedCap, Finset.sum_ite_eq']

/-- The appended row counts sources of one block/label in a selected list. -/
theorem labelAugmentedUse_rowLoad_label
    (baseUse : Source → State → Row → ℝ)
    (blockOf : Source → Block) (stateLabel : State → Label)
    (choice : Source → State) (b : Block) (l : Label) :
    WeightedEdgeColoring.FiniteCategoricalSelection.rowLoad
        (labelAugmentedUse baseUse blockOf stateLabel) (Sum.inr (b, l)) choice =
      ∑ src : Source,
        if blockOf src = b ∧ stateLabel (choice src) = l then 1 else 0 := by
  rfl

/-- For every label row, both its fractional mean and complementary mean
are bounded by the number of sources in that block. -/
theorem labelAugmented_labelMean_bounds
    (prob : Source → State → ℝ)
    (hprob0 : ∀ src state, 0 ≤ prob src state)
    (hprobSum : ∀ src, ∑ state, prob src state = 1)
    (baseUse : Source → State → Row → ℝ)
    (baseCap : Source → Row → ℝ)
    (blockOf : Source → Block) (stateLabel : State → Label)
    (b : Block) (l : Label) :
    0 ≤ WeightedEdgeColoring.FiniteCategoricalSelection.rowMean prob
      (labelAugmentedUse baseUse blockOf stateLabel) (Sum.inr (b, l)) ∧
    WeightedEdgeColoring.FiniteCategoricalSelection.rowMean prob
      (labelAugmentedUse baseUse blockOf stateLabel) (Sum.inr (b, l)) ≤
        ∑ src : Source, if blockOf src = b then (1 : ℝ) else 0 := by
  constructor
  · unfold WeightedEdgeColoring.FiniteCategoricalSelection.rowMean
    apply Finset.sum_nonneg
    intro src _
    apply Finset.sum_nonneg
    intro state _
    apply mul_nonneg (hprob0 src state)
    dsimp [labelAugmentedUse]
    split_ifs <;> norm_num
  · unfold WeightedEdgeColoring.FiniteCategoricalSelection.rowMean
    apply Finset.sum_le_sum
    intro src _
    by_cases hb : blockOf src = b
    · simp only [hb, ite_true]
      calc
        (∑ state : State,
            prob src state *
              labelAugmentedUse baseUse blockOf stateLabel src state (Sum.inr (b, l))) ≤
          ∑ state : State, prob src state := by
            apply Finset.sum_le_sum
            intro state _
            by_cases hl : stateLabel state = l
            · simp [labelAugmentedUse, hb, hl]
            · simpa [labelAugmentedUse, hb, hl] using hprob0 src state
        _ = 1 := hprobSum src
    · simp [labelAugmentedUse, hb]

/-- Append all block/label counts to an existing two-sided list selector.
The selector's column bound rises by exactly the fixed label-menu size;
the bound does not depend on the number of blocks or graph vertices. -/
theorem exists_supported_choice_with_blockLabelCounts
    (R C : ℝ) (hR : 0 < R) (hC : 0 ≤ C) (hC1 : 1 ≤ C)
    (K : ℕ) (hK : 0 < K) (hRK : R ≤ K)
    (prob : Source → State → ℝ) (dummyProb : State → ℝ)
    (baseUse : Source → State → Row → ℝ)
    (baseCap : Source → Row → ℝ)
    (blockOf : Source → Block) (stateLabel : State → Label)
    (hprob0 : ∀ src state, 0 ≤ prob src state)
    (hprobSum : ∀ src, ∑ state, prob src state = 1)
    (hdummy0 : ∀ state, 0 ≤ dummyProb state)
    (hdummySum : ∑ state, dummyProb state = 1)
    (hbaseUse0 : ∀ src state row, 0 ≤ baseUse src state row)
    (hbaseUseCap : ∀ src state row,
      baseUse src state row ≤ baseCap src row)
    (hbaseCap1 : ∀ src row, baseCap src row ≤ 1)
    (hbaseMeanUpper : ∀ row,
      WeightedEdgeColoring.FiniteCategoricalSelection.rowMean prob baseUse row ≤ R)
    (hbaseMeanLower : ∀ row,
      (∑ src, baseCap src row) -
        WeightedEdgeColoring.FiniteCategoricalSelection.rowMean prob baseUse row ≤ R)
    (hbaseColumn : ∀ src, (∑ row, baseCap src row) ≤ C)
    (hblockCount : ∀ b,
      (∑ src : Source, if blockOf src = b then (1 : ℝ) else 0) ≤ R) :
    ∃ choice : Source → State,
      (∀ src, 0 < prob src (choice src)) ∧
      (∀ row : Row,
        |WeightedEdgeColoring.FiniteCategoricalSelection.rowLoad baseUse row choice -
          WeightedEdgeColoring.FiniteCategoricalSelection.rowMean prob baseUse row| <
            WeightedEdgeColoring.FinitePartialResamplingNumerics.packingDeviation
              R (C + Fintype.card Label)) ∧
      ∀ b l,
        |(∑ src : Source,
            if blockOf src = b ∧ stateLabel (choice src) = l
            then (1 : ℝ) else 0) -
          WeightedEdgeColoring.FiniteCategoricalSelection.rowMean prob
            (labelAugmentedUse baseUse blockOf stateLabel)
            (Sum.inr (b, l))| <
          WeightedEdgeColoring.FinitePartialResamplingNumerics.packingDeviation
            R (C + Fintype.card Label) := by
  let augUse := labelAugmentedUse baseUse blockOf stateLabel
  let augCap : Source → (Row ⊕ (Block × Label)) → ℝ :=
    labelAugmentedCap baseCap blockOf
  have hmeanUpper : ∀ row : Row ⊕ (Block × Label),
      WeightedEdgeColoring.FiniteCategoricalSelection.rowMean prob augUse row ≤ R := by
    intro row
    cases row with
    | inl row => simpa [augUse, WeightedEdgeColoring.FiniteCategoricalSelection.rowMean,
        labelAugmentedUse] using hbaseMeanUpper row
    | inr bl =>
        exact (labelAugmented_labelMean_bounds prob hprob0 hprobSum
          baseUse baseCap blockOf stateLabel bl.1 bl.2).2.trans
          (hblockCount bl.1)
  have hmeanLower : ∀ row : Row ⊕ (Block × Label),
      (∑ src, augCap src row) -
        WeightedEdgeColoring.FiniteCategoricalSelection.rowMean prob augUse row ≤ R := by
    intro row
    cases row with
    | inl row => simpa [augUse, augCap,
        WeightedEdgeColoring.FiniteCategoricalSelection.rowMean,
        labelAugmentedUse, labelAugmentedCap] using hbaseMeanLower row
    | inr bl =>
        have hnonneg := (labelAugmented_labelMean_bounds prob hprob0 hprobSum
          baseUse baseCap blockOf stateLabel bl.1 bl.2).1
        have hc := hblockCount bl.1
        change (∑ src : Source,
          if blockOf src = bl.1 then (1 : ℝ) else 0) -
            WeightedEdgeColoring.FiniteCategoricalSelection.rowMean prob
              (labelAugmentedUse baseUse blockOf stateLabel)
              (Sum.inr bl) ≤ R
        linarith
  have hcolumn : ∀ src, (∑ row, augCap src row) ≤
      C + Fintype.card Label := by
    intro src
    rw [show (∑ row, augCap src row) =
      (∑ row : Row, baseCap src row) + (Fintype.card Label : ℝ) from
      labelAugmentedCap_column baseCap blockOf src]
    exact add_le_add (hbaseColumn src) le_rfl
  have hCtotal : 0 ≤ C + (Fintype.card Label : ℝ) := by positivity
  have hCtotal1 : 1 ≤ C + (Fintype.card Label : ℝ) := by
    have : 0 ≤ (Fintype.card Label : ℝ) := Nat.cast_nonneg _
    linarith
  obtain ⟨choice, hsupport, hrows⟩ :=
    WeightedEdgeColoring.WeightedMomentTwoSidedSelection.exists_supported_choice_abs_rowLoad_sub_mean_lt_deviation
      R (C + Fintype.card Label) hR hCtotal hCtotal1 K hK hRK
      prob dummyProb augUse augCap hprob0 hprobSum hdummy0 hdummySum
      (labelAugmentedUse_nonneg baseUse hbaseUse0 blockOf stateLabel)
      (labelAugmentedUse_le_cap baseUse baseCap hbaseUseCap blockOf stateLabel)
      (labelAugmentedCap_le_one baseCap hbaseCap1 blockOf)
      hmeanUpper hmeanLower hcolumn
  refine ⟨choice, hsupport, ?_, ?_⟩
  · intro row
    simpa [augUse, labelAugmentedUse,
      WeightedEdgeColoring.FiniteCategoricalSelection.rowLoad,
      WeightedEdgeColoring.FiniteCategoricalSelection.rowMean] using hrows (Sum.inl row)
  · intro b l
    simpa [augUse, labelAugmentedUse,
      WeightedEdgeColoring.FiniteCategoricalSelection.rowLoad] using hrows (Sum.inr (b, l))

end WeightedEdgeColoring.Subtwo
