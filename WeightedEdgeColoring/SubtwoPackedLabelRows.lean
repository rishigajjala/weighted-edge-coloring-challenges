import WeightedEdgeColoring.SubtwoLabelListSelection

/-!
# Endpoint-label rows for packed color words

A categorical state at a block source may encode an entire word of colors.
Its endpoint label is therefore a *word* of labels, not one label.  We append
one normalized count row for each vertex and label.  Normalization by the
fixed word length keeps every source's row cap at one, and the extra column
cost is exactly the label alphabet size.
-/

open scoped BigOperators

namespace WeightedEdgeColoring.Subtwo

noncomputable section

variable {Source State Row Vertex Label : Type*}
  [Fintype Source] [DecidableEq Source]
  [Fintype State] [DecidableEq State]
  [Fintype Row] [DecidableEq Row]
  [Fintype Vertex] [DecidableEq Vertex]
  [Fintype Label] [DecidableEq Label]

/-- Fraction of coordinates in a packed word assigned to one endpoint
label, charged to the source vertex. -/
def packedLabelUse {k : ℕ} (hk : 0 < k)
    (vertexOf : Source → Vertex)
    (coordinateLabel : Source → State → Fin k → Label)
    (src : Source) (state : State) (vl : Vertex × Label) : ℝ :=
  if vertexOf src = vl.1 then
    (∑ c : Fin k,
      if coordinateLabel src state c = vl.2 then (1 : ℝ) else 0) / k
  else 0

/-- A source contributes at most one normalized unit to each label row. -/
def packedLabelCap
    (vertexOf : Source → Vertex)
    (src : Source) (vl : Vertex × Label) : ℝ :=
  if vertexOf src = vl.1 then 1 else 0

theorem packedLabelUse_nonneg {k : ℕ} (hk : 0 < k)
    (vertexOf : Source → Vertex)
    (coordinateLabel : Source → State → Fin k → Label)
    (src : Source) (state : State) (vl : Vertex × Label) :
    0 ≤ packedLabelUse hk vertexOf coordinateLabel src state vl := by
  unfold packedLabelUse
  split
  · apply div_nonneg
    · exact Finset.sum_nonneg fun c _ ↦ by split_ifs <;> norm_num
    · exact Nat.cast_nonneg k
  · exact le_rfl

theorem packedLabelUse_le_cap {k : ℕ} (hk : 0 < k)
    (vertexOf : Source → Vertex)
    (coordinateLabel : Source → State → Fin k → Label)
    (src : Source) (state : State) (vl : Vertex × Label) :
    packedLabelUse hk vertexOf coordinateLabel src state vl ≤
      packedLabelCap vertexOf src vl := by
  by_cases hv : vertexOf src = vl.1
  · simp only [packedLabelUse, packedLabelCap, hv, ite_true]
    have hkR : (0 : ℝ) < k := by exact_mod_cast hk
    apply (div_le_one hkR).2
    calc
      (∑ c : Fin k,
          if coordinateLabel src state c = vl.2 then (1 : ℝ) else 0) ≤
          ∑ _c : Fin k, (1 : ℝ) := by
        apply Finset.sum_le_sum
        intro c _
        split_ifs <;> norm_num
      _ = k := by simp
  · simp [packedLabelUse, packedLabelCap, hv]

theorem packedLabelCap_le_one
    (vertexOf : Source → Vertex)
    (src : Source) (vl : Vertex × Label) :
    packedLabelCap vertexOf src vl ≤ 1 := by
  simp [packedLabelCap]
  split_ifs <;> norm_num

/-- Augment arbitrary existing selector rows by normalized packed-label
counts. -/
def packedLabelAugmentedUse {k : ℕ} (hk : 0 < k)
    (baseUse : Source → State → Row → ℝ)
    (vertexOf : Source → Vertex)
    (coordinateLabel : Source → State → Fin k → Label) :
    Source → State → (Row ⊕ (Vertex × Label)) → ℝ
  | src, state, Sum.inl row => baseUse src state row
  | src, state, Sum.inr vl =>
      packedLabelUse hk vertexOf coordinateLabel src state vl

def packedLabelAugmentedCap
    (baseCap : Source → Row → ℝ)
    (vertexOf : Source → Vertex) :
    Source → (Row ⊕ (Vertex × Label)) → ℝ
  | src, Sum.inl row => baseCap src row
  | src, Sum.inr vl => packedLabelCap vertexOf src vl

theorem packedLabelAugmentedUse_nonneg {k : ℕ} (hk : 0 < k)
    (baseUse : Source → State → Row → ℝ)
    (hbase : ∀ src state row, 0 ≤ baseUse src state row)
    (vertexOf : Source → Vertex)
    (coordinateLabel : Source → State → Fin k → Label) :
    ∀ src state row,
      0 ≤ packedLabelAugmentedUse hk baseUse vertexOf coordinateLabel
        src state row := by
  intro src state row
  cases row with
  | inl row => exact hbase src state row
  | inr vl => exact packedLabelUse_nonneg hk vertexOf coordinateLabel src state vl

theorem packedLabelAugmentedUse_le_cap {k : ℕ} (hk : 0 < k)
    (baseUse : Source → State → Row → ℝ)
    (baseCap : Source → Row → ℝ)
    (hbase : ∀ src state row, baseUse src state row ≤ baseCap src row)
    (vertexOf : Source → Vertex)
    (coordinateLabel : Source → State → Fin k → Label) :
    ∀ src state row,
      packedLabelAugmentedUse hk baseUse vertexOf coordinateLabel
        src state row ≤ packedLabelAugmentedCap baseCap vertexOf src row := by
  intro src state row
  cases row with
  | inl row => exact hbase src state row
  | inr vl => exact packedLabelUse_le_cap hk vertexOf coordinateLabel src state vl

theorem packedLabelAugmentedCap_le_one
    (baseCap : Source → Row → ℝ)
    (hbase : ∀ src row, baseCap src row ≤ 1)
    (vertexOf : Source → Vertex) :
    ∀ src (row : Row ⊕ (Vertex × Label)),
      packedLabelAugmentedCap baseCap vertexOf src row ≤ 1 := by
  intro src row
  cases row with
  | inl row => exact hbase src row
  | inr vl => exact packedLabelCap_le_one vertexOf src vl

theorem packedLabelAugmentedCap_column
    (baseCap : Source → Row → ℝ)
    (vertexOf : Source → Vertex) (src : Source) :
    (∑ row : Row ⊕ (Vertex × Label),
      packedLabelAugmentedCap baseCap vertexOf src row) =
      (∑ row : Row, baseCap src row) + (Fintype.card Label : ℝ) := by
  rw [Fintype.sum_sum_type, Fintype.sum_prod_type]
  simp [packedLabelAugmentedCap, packedLabelCap, Finset.sum_ite_eq']
  calc
    (∑ x : Vertex,
      ((if vertexOf src = x then (Finset.univ : Finset Label)
        else ∅).card : ℝ)) =
        ∑ x : Vertex,
          if vertexOf src = x then (Fintype.card Label : ℝ) else 0 := by
      apply Finset.sum_congr rfl
      intro x _
      by_cases hx : vertexOf src = x <;> simp [hx]
    _ = Fintype.card Label := by simp


/-- The normalized label-row mean lies between zero and the number of
sources at that vertex. -/
theorem packedLabelAugmented_labelMean_bounds
    {k : ℕ} (hk : 0 < k)
    (prob : Source → State → ℝ)
    (hprob0 : ∀ src state, 0 ≤ prob src state)
    (hprobSum : ∀ src, ∑ state, prob src state = 1)
    (baseUse : Source → State → Row → ℝ)
    (vertexOf : Source → Vertex)
    (coordinateLabel : Source → State → Fin k → Label)
    (v : Vertex) (label : Label) :
    0 ≤ WeightedEdgeColoring.FiniteCategoricalSelection.rowMean prob
      (packedLabelAugmentedUse hk baseUse vertexOf coordinateLabel)
      (Sum.inr (v, label)) ∧
    WeightedEdgeColoring.FiniteCategoricalSelection.rowMean prob
      (packedLabelAugmentedUse hk baseUse vertexOf coordinateLabel)
      (Sum.inr (v, label)) ≤
        ∑ src : Source, if vertexOf src = v then (1 : ℝ) else 0 := by
  constructor
  · unfold WeightedEdgeColoring.FiniteCategoricalSelection.rowMean
    apply Finset.sum_nonneg
    intro src _
    apply Finset.sum_nonneg
    intro state _
    exact mul_nonneg (hprob0 src state)
      (packedLabelUse_nonneg hk vertexOf coordinateLabel src state (v, label))
  · unfold WeightedEdgeColoring.FiniteCategoricalSelection.rowMean
    apply Finset.sum_le_sum
    intro src _
    calc
      (∑ state : State,
        prob src state *
          packedLabelAugmentedUse hk baseUse vertexOf coordinateLabel
            src state (Sum.inr (v, label))) ≤
        ∑ state : State,
          prob src state * packedLabelCap vertexOf src (v, label) := by
        apply Finset.sum_le_sum
        intro state _
        exact mul_le_mul_of_nonneg_left
          (packedLabelUse_le_cap hk vertexOf coordinateLabel
            src state (v, label)) (hprob0 src state)
      _ = if vertexOf src = v then (1 : ℝ) else 0 := by
        rw [← Finset.sum_mul, hprobSum]
        simp [packedLabelCap]

/-- The decoded normalized count at a selected packed word is exactly the
selected label count divided by the fixed number of colors in the word. -/
theorem packedLabel_rowLoad_eq_count_div
    {k : ℕ} (hk : 0 < k)
    (baseUse : Source → State → Row → ℝ)
    (vertexOf : Source → Vertex)
    (coordinateLabel : Source → State → Fin k → Label)
    (choice : Source → State) (v : Vertex) (label : Label) :
    WeightedEdgeColoring.FiniteCategoricalSelection.rowLoad
      (packedLabelAugmentedUse hk baseUse vertexOf coordinateLabel)
      (Sum.inr (v, label)) choice =
      (∑ src : Source,
        if vertexOf src = v then
          ∑ c : Fin k,
            if coordinateLabel src (choice src) c = label
              then (1 : ℝ) else 0
        else 0) / k := by
  unfold WeightedEdgeColoring.FiniteCategoricalSelection.rowLoad
  rw [Finset.sum_div]
  apply Finset.sum_congr rfl
  intro src _
  by_cases hv : vertexOf src = v <;>
    simp [packedLabelAugmentedUse, packedLabelUse, hv]

/-- Two-sided categorical selection with one extra normalized label-count
row per vertex/label pair.  The added column cost is `|Label|`, independent
of the number of packed colors. -/
theorem exists_supported_choice_with_packedLabelCounts
    {k : ℕ} (hk : 0 < k)
    (R C : ℝ) (hR : 0 < R) (hC : 0 ≤ C) (hC1 : 1 ≤ C)
    (K : ℕ) (hK : 0 < K) (hRK : R ≤ K)
    (prob : Source → State → ℝ) (dummyProb : State → ℝ)
    (baseUse : Source → State → Row → ℝ)
    (baseCap : Source → Row → ℝ)
    (vertexOf : Source → Vertex)
    (coordinateLabel : Source → State → Fin k → Label)
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
    (hvertexCount : ∀ v,
      (∑ src : Source, if vertexOf src = v then (1 : ℝ) else 0) ≤ R) :
    ∃ choice : Source → State,
      (∀ src, 0 < prob src (choice src)) ∧
      (∀ row : Row,
        |WeightedEdgeColoring.FiniteCategoricalSelection.rowLoad baseUse row choice -
          WeightedEdgeColoring.FiniteCategoricalSelection.rowMean prob baseUse row| <
            WeightedEdgeColoring.FinitePartialResamplingNumerics.packingDeviation
              R (C + Fintype.card Label)) ∧
      ∀ v label,
        |(∑ src : Source,
            if vertexOf src = v then
              ∑ c : Fin k,
                if coordinateLabel src (choice src) c = label
                  then (1 : ℝ) else 0
            else 0) / k -
          WeightedEdgeColoring.FiniteCategoricalSelection.rowMean prob
            (packedLabelAugmentedUse hk baseUse vertexOf coordinateLabel)
            (Sum.inr (v, label))| <
          WeightedEdgeColoring.FinitePartialResamplingNumerics.packingDeviation
            R (C + Fintype.card Label) := by
  let augUse := packedLabelAugmentedUse hk baseUse vertexOf coordinateLabel
  let augCap : Source → (Row ⊕ (Vertex × Label)) → ℝ :=
    packedLabelAugmentedCap baseCap vertexOf
  have hmeanUpper : ∀ row : Row ⊕ (Vertex × Label),
      WeightedEdgeColoring.FiniteCategoricalSelection.rowMean prob augUse row ≤ R := by
    intro row
    cases row with
    | inl row => simpa [augUse, WeightedEdgeColoring.FiniteCategoricalSelection.rowMean,
        packedLabelAugmentedUse] using hbaseMeanUpper row
    | inr vl =>
        exact (packedLabelAugmented_labelMean_bounds hk prob
          hprob0 hprobSum baseUse vertexOf coordinateLabel vl.1 vl.2).2.trans
          (hvertexCount vl.1)
  have hmeanLower : ∀ row : Row ⊕ (Vertex × Label),
      (∑ src, augCap src row) -
        WeightedEdgeColoring.FiniteCategoricalSelection.rowMean prob augUse row ≤ R := by
    intro row
    cases row with
    | inl row => simpa [augUse, augCap,
        WeightedEdgeColoring.FiniteCategoricalSelection.rowMean,
        packedLabelAugmentedUse, packedLabelAugmentedCap] using
          hbaseMeanLower row
    | inr vl =>
        have hnonneg := (packedLabelAugmented_labelMean_bounds hk prob
          hprob0 hprobSum baseUse vertexOf coordinateLabel vl.1 vl.2).1
        have hc := hvertexCount vl.1
        change (∑ src : Source,
          if vertexOf src = vl.1 then (1 : ℝ) else 0) -
            WeightedEdgeColoring.FiniteCategoricalSelection.rowMean prob
              (packedLabelAugmentedUse hk baseUse vertexOf coordinateLabel)
              (Sum.inr vl) ≤ R
        linarith
  have hcolumn : ∀ src, (∑ row, augCap src row) ≤
      C + Fintype.card Label := by
    intro src
    rw [show (∑ row, augCap src row) =
      (∑ row : Row, baseCap src row) + (Fintype.card Label : ℝ) from
      packedLabelAugmentedCap_column baseCap vertexOf src]
    exact add_le_add (hbaseColumn src) le_rfl
  have hCtotal : 0 ≤ C + (Fintype.card Label : ℝ) := by positivity
  have hCtotal1 : 1 ≤ C + (Fintype.card Label : ℝ) := by
    have : 0 ≤ (Fintype.card Label : ℝ) := Nat.cast_nonneg _
    linarith
  obtain ⟨choice, hsupport, hrows⟩ :=
    WeightedEdgeColoring.WeightedMomentTwoSidedSelection.exists_supported_choice_abs_rowLoad_sub_mean_lt_deviation
      R (C + Fintype.card Label) hR hCtotal hCtotal1 K hK hRK
      prob dummyProb augUse augCap hprob0 hprobSum hdummy0 hdummySum
      (packedLabelAugmentedUse_nonneg hk baseUse hbaseUse0 vertexOf coordinateLabel)
      (packedLabelAugmentedUse_le_cap hk baseUse baseCap hbaseUseCap vertexOf coordinateLabel)
      (packedLabelAugmentedCap_le_one baseCap hbaseCap1 vertexOf)
      hmeanUpper hmeanLower hcolumn
  refine ⟨choice, hsupport, ?_, ?_⟩
  · intro row
    simpa [augUse, packedLabelAugmentedUse,
      WeightedEdgeColoring.FiniteCategoricalSelection.rowLoad,
      WeightedEdgeColoring.FiniteCategoricalSelection.rowMean] using hrows (Sum.inl row)
  · intro v label
    simpa [augUse, packedLabel_rowLoad_eq_count_div] using
      hrows (Sum.inr (v, label))

end

end WeightedEdgeColoring.Subtwo
