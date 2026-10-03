import WeightedEdgeColoring.MultigraphColorDependentExtendedProfileWordPadding
import WeightedEdgeColoring.FinitePartialResamplingPackingSelection
import WeightedEdgeColoring.FinitePartialResamplingPackingMeanSelection
import WeightedEdgeColoring.FinitePartialResamplingNumericsBounds

/-!
# Capacity arrays for color-dependent extended-profile words

Rows are indexed by a color and a finite row type for that color.  An atom
coefficient reads one extended state at `(v,c)`.  The packed-word coefficient
decodes exactly coordinate `c`.  Consequently its product-law row mean is
the original atom mean, while a uniform one-coordinate column bound `K`
becomes the explicit whole-word column bound `|Color| K`.
-/

namespace WeightedEdgeColoring

open scoped BigOperators

noncomputable section

namespace WeightedMultigraph

universe u w₁ w₂

variable (G : WeightedMultigraph.{u})
variable {Color : Type w₁} [Fintype Color] [DecidableEq Color]
variable {s β q r : ℝ} {hβ : 0 < β} {hr : 0 < r}
variable {proposal : G.E → Color → ℝ}
variable (R : ∀ v c, G.BoundedProfileRealization
  (fun e : G.StarEdge v ↦ proposal e.1 c) s β q r hβ hr)

variable (RowAt : Color → Type w₂)
variable [∀ c, Fintype (RowAt c)] [∀ c, DecidableEq (RowAt c)]

/-- The disjoint union of all per-color capacity rows. -/
abbrev ColorDependentExtendedProfileCapacityRow
    (_G : WeightedMultigraph.{u}) :=
  Σ c : Color, RowAt c

/-- Lift one-color atom coefficients to a packed whole-word source. -/
def colorDependentExtendedProfileWordCapacityUse
    (atomUse : ∀ v c,
      G.ColorDependentExtendedProfileState R v c → RowAt c → ℝ)
    (v : G.V)
    (a : G.ColorDependentExtendedProfilePackedWordState
      (Color := Color) (β := β) (q := q) (r := r))
    (row : G.ColorDependentExtendedProfileCapacityRow RowAt) : ℝ :=
  atomUse v row.1
    (G.decodeColorDependentExtendedProfileWord R v a row.1) row.2

theorem colorDependentWordCapacityUse_nonneg
    (atomUse : ∀ v c,
      G.ColorDependentExtendedProfileState R v c → RowAt c → ℝ)
    (hatom0 : ∀ v c z row, 0 ≤ atomUse v c z row)
    (v : G.V)
    (a : G.ColorDependentExtendedProfilePackedWordState
      (Color := Color) (β := β) (q := q) (r := r))
    (row : G.ColorDependentExtendedProfileCapacityRow RowAt) :
    0 ≤ G.colorDependentExtendedProfileWordCapacityUse R RowAt atomUse
      v a row := by
  exact hatom0 v row.1
    (G.decodeColorDependentExtendedProfileWord R v a row.1) row.2

theorem colorDependentWordCapacityUse_le_one
    (atomUse : ∀ v c,
      G.ColorDependentExtendedProfileState R v c → RowAt c → ℝ)
    (hatom1 : ∀ v c z row, atomUse v c z row ≤ 1)
    (v : G.V)
    (a : G.ColorDependentExtendedProfilePackedWordState
      (Color := Color) (β := β) (q := q) (r := r))
    (row : G.ColorDependentExtendedProfileCapacityRow RowAt) :
    G.colorDependentExtendedProfileWordCapacityUse R RowAt atomUse
      v a row ≤ 1 := by
  exact hatom1 v row.1
    (G.decodeColorDependentExtendedProfileWord R v a row.1) row.2

/-- Exact product mean of one per-color capacity row. -/
theorem colorDependentWordCapacity_rowMean_eq
    (omega : ℝ)
    (atomUse : ∀ v c,
      G.ColorDependentExtendedProfileState R v c → RowAt c → ℝ)
    (row : G.ColorDependentExtendedProfileCapacityRow RowAt) :
    FiniteCategoricalSelection.rowMean
        (G.paddedColorDependentExtendedProfileWordProbability R omega)
        (G.colorDependentExtendedProfileWordCapacityUse R RowAt atomUse)
        row =
      ∑ v, ∑ z : G.ColorDependentExtendedProfileState R v row.1,
        G.smoothedColorDependentExtendedProfileProbability
            R omega v row.1 z * atomUse v row.1 z row.2 := by
  unfold FiniteCategoricalSelection.rowMean
  apply Finset.sum_congr rfl
  intro v _hv
  exact G.sum_paddedColorDependentProbability_mul_decode_coordinate
    R omega v row.1 (fun z ↦ atomUse v row.1 z row.2)

/-- A uniform atom-row mean bound transfers with no loss to packed words. -/
theorem colorDependentWordCapacity_rowMean_le
    (omega meanBound : ℝ)
    (atomUse : ∀ v c,
      G.ColorDependentExtendedProfileState R v c → RowAt c → ℝ)
    (hmean : ∀ c row,
      (∑ v, ∑ z : G.ColorDependentExtendedProfileState R v c,
        G.smoothedColorDependentExtendedProfileProbability R omega v c z *
          atomUse v c z row) ≤ meanBound)
    (row : G.ColorDependentExtendedProfileCapacityRow RowAt) :
    FiniteCategoricalSelection.rowMean
        (G.paddedColorDependentExtendedProfileWordProbability R omega)
        (G.colorDependentExtendedProfileWordCapacityUse R RowAt atomUse)
        row ≤ meanBound := by
  rw [G.colorDependentWordCapacity_rowMean_eq R RowAt omega atomUse row]
  exact hmean row.1 row.2

/-- The packed-word column sum is exactly the sum of the decoded
one-coordinate column sums. -/
theorem sum_colorDependentWordCapacityUse_eq
    (atomUse : ∀ v c,
      G.ColorDependentExtendedProfileState R v c → RowAt c → ℝ)
    (v : G.V)
    (a : G.ColorDependentExtendedProfilePackedWordState
      (Color := Color) (β := β) (q := q) (r := r)) :
    (∑ row : G.ColorDependentExtendedProfileCapacityRow RowAt,
      G.colorDependentExtendedProfileWordCapacityUse R RowAt atomUse
        v a row) =
      ∑ c : Color, ∑ row : RowAt c,
        atomUse v c
          (G.decodeColorDependentExtendedProfileWord R v a c) row := by
  rw [Fintype.sum_sigma]
  rfl

/-- Uniform product column bound.  A word has one atom column for every
color, hence the only loss is the explicit factor `|Color|`. -/
theorem sum_colorDependentWordCapacityUse_le_card_mul
    (atomUse : ∀ v c,
      G.ColorDependentExtendedProfileState R v c → RowAt c → ℝ)
    (columnBound : ℝ)
    (hcolumn : ∀ v c z, ∑ row : RowAt c, atomUse v c z row ≤ columnBound)
    (v : G.V)
    (a : G.ColorDependentExtendedProfilePackedWordState
      (Color := Color) (β := β) (q := q) (r := r)) :
    (∑ row : G.ColorDependentExtendedProfileCapacityRow RowAt,
      G.colorDependentExtendedProfileWordCapacityUse R RowAt atomUse
        v a row) ≤ Fintype.card Color * columnBound := by
  rw [G.sum_colorDependentWordCapacityUse_eq R RowAt atomUse v a]
  calc
    (∑ c : Color, ∑ row : RowAt c,
        atomUse v c
          (G.decodeColorDependentExtendedProfileWord R v a c) row) ≤
      ∑ _c : Color, columnBound := by
        apply Finset.sum_le_sum
        intro c _hc
        exact hcolumn v c
          (G.decodeColorDependentExtendedProfileWord R v a c)
    _ = Fintype.card Color * columnBound := by simp

/-- Apply the finite packing selector to the color-dependent product words.
All representation and product-law work is discharged by the preceding
exact identities. -/
theorem exists_colorDependentExtendedProfileWord_capacity_lt
    (omega meanBound columnBound : ℝ)
    (hs : 0 ≤ s) (hq : 0 ≤ q) (hr0 : 0 ≤ r)
    (hleft : 0 ≤ 1 - s * (1 + q + r))
    (homega0 : 0 < omega) (homega1 : omega ≤ 1)
    (hmeanBound : 0 < meanBound) (hcolumnBound : 0 ≤ columnBound)
    (atomUse : ∀ v c,
      G.ColorDependentExtendedProfileState R v c → RowAt c → ℝ)
    (hatom0 : ∀ v c z row, 0 ≤ atomUse v c z row)
    (hatom1 : ∀ v c z row, atomUse v c z row ≤ 1)
    (hmean : ∀ c row,
      (∑ v, ∑ z : G.ColorDependentExtendedProfileState R v c,
        G.smoothedColorDependentExtendedProfileProbability R omega v c z *
          atomUse v c z row) ≤ meanBound)
    (hcolumn : ∀ v c z,
      ∑ row : RowAt c, atomUse v c z row ≤ columnBound) :
    ∃ word : ∀ v, G.ColorDependentExtendedProfileWord R v,
      (∀ v,
        0 < G.colorDependentExtendedProfileWordMass R omega v (word v)) ∧
      ∀ row : G.ColorDependentExtendedProfileCapacityRow RowAt,
        (∑ v, atomUse v row.1 (word v row.1) row.2) <
          meanBound +
            FinitePartialResamplingNumerics.packingDeviation meanBound
              (Fintype.card Color * columnBound) := by
  let prob := G.paddedColorDependentExtendedProfileWordProbability R omega
  let use := G.colorDependentExtendedProfileWordCapacityUse R RowAt atomUse
  have hcolumnWhole : 0 ≤ Fintype.card Color * columnBound :=
    mul_nonneg (Nat.cast_nonneg _) hcolumnBound
  obtain ⟨choice, hchoicePos, hchoiceLoad⟩ :=
    FiniteCategoricalSelection.exists_supported_choice_rowLoad_lt_packingThreshold
      meanBound (Fintype.card Color * columnBound)
      hmeanBound hcolumnWhole prob use
      (G.paddedColorDependentExtendedProfileWordProbability_nonneg R
        hs hq hr0 hleft homega0 homega1)
      (G.sum_paddedColorDependentExtendedProfileWordProbability R omega)
      (G.colorDependentWordCapacityUse_nonneg R RowAt atomUse hatom0)
      (G.colorDependentWordCapacityUse_le_one R RowAt atomUse hatom1)
      (G.colorDependentWordCapacity_rowMean_le
        R RowAt omega meanBound atomUse hmean)
      (G.sum_colorDependentWordCapacityUse_le_card_mul
        R RowAt atomUse columnBound hcolumn)
  have hdecode : ∀ v, ∃ word : G.ColorDependentExtendedProfileWord R v,
      G.encodeColorDependentExtendedProfileWord R v word = choice v ∧
        0 < G.colorDependentExtendedProfileWordMass R omega v word := by
    intro v
    exact G.exists_colorDependentExtendedProfileWord_of_padded_pos R
      hs hq hr0 hleft homega0 homega1 v (choice v) (hchoicePos v)
  let word : ∀ v, G.ColorDependentExtendedProfileWord R v :=
    fun v ↦ Classical.choose (hdecode v)
  have hcode : ∀ v,
      G.encodeColorDependentExtendedProfileWord R v (word v) = choice v := by
    intro v
    exact (Classical.choose_spec (hdecode v)).1
  refine ⟨word, ?_, ?_⟩
  · intro v
    exact (Classical.choose_spec (hdecode v)).2
  · intro row
    have hload := hchoiceLoad row
    have hthreshold :=
      FinitePartialResamplingNumerics.packingThreshold_le_base_add_deviation
        hmeanBound hcolumnWhole
    calc
      (∑ v, atomUse v row.1 (word v row.1) row.2) =
          FiniteCategoricalSelection.rowLoad use row choice := by
        unfold FiniteCategoricalSelection.rowLoad use
          colorDependentExtendedProfileWordCapacityUse
        apply Finset.sum_congr rfl
        intro v _hv
        rw [← hcode v]
        simp
      _ < FinitePartialResamplingNumerics.packingThreshold meanBound
          (Fintype.card Color * columnBound) := hload
      _ ≤ meanBound +
          FinitePartialResamplingNumerics.packingDeviation meanBound
            (Fintype.card Color * columnBound) := hthreshold

/-- Mean-relative version of the color-dependent word selector.  The common
bound controls only the deviation; every selected row is compared with its
own exact product-law mean.  This distinction is essential for a selected
tiny state whose reservoir size is zero. -/
theorem exists_colorDependentExtendedProfileWord_rowLoad_lt_rowMean_add_deviation
    (omega meanBound columnBound : ℝ)
    (hs : 0 ≤ s) (hq : 0 ≤ q) (hr0 : 0 ≤ r)
    (hleft : 0 ≤ 1 - s * (1 + q + r))
    (homega0 : 0 < omega) (homega1 : omega ≤ 1)
    (hmeanBound : 0 < meanBound) (hcolumnBound : 0 ≤ columnBound)
    (hcolumnOne : 1 ≤ Fintype.card Color * columnBound)
    (K : ℕ) (hK : 0 < K) (hmeanK : meanBound ≤ K)
    (atomUse : ∀ v c,
      G.ColorDependentExtendedProfileState R v c → RowAt c → ℝ)
    (hatom0 : ∀ v c z row, 0 ≤ atomUse v c z row)
    (hatom1 : ∀ v c z row, atomUse v c z row ≤ 1)
    (hmean : ∀ c row,
      (∑ v, ∑ z : G.ColorDependentExtendedProfileState R v c,
        G.smoothedColorDependentExtendedProfileProbability R omega v c z *
          atomUse v c z row) ≤ meanBound)
    (hcolumn : ∀ v c z,
      ∑ row : RowAt c, atomUse v c z row ≤ columnBound) :
    ∃ word : ∀ v, G.ColorDependentExtendedProfileWord R v,
      (∀ v,
        0 < G.colorDependentExtendedProfileWordMass R omega v (word v)) ∧
      ∀ row : G.ColorDependentExtendedProfileCapacityRow RowAt,
        (∑ v, atomUse v row.1 (word v row.1) row.2) <
          (∑ v, ∑ z : G.ColorDependentExtendedProfileState R v row.1,
            G.smoothedColorDependentExtendedProfileProbability
                R omega v row.1 z * atomUse v row.1 z row.2) +
            FinitePartialResamplingNumerics.packingDeviation meanBound
              (Fintype.card Color * columnBound) := by
  let State := G.ColorDependentExtendedProfilePackedWordState
    (Color := Color) (β := β) (q := q) (r := r)
  let prob := G.paddedColorDependentExtendedProfileWordProbability R omega
  let use := G.colorDependentExtendedProfileWordCapacityUse R RowAt atomUse
  let dummyProb : State → ℝ := fun _ ↦ 1 / Fintype.card State
  have hStateCard : 0 < Fintype.card State := by
    unfold State ColorDependentExtendedProfilePackedWordState
      FiniteDependentWordPadding.PackedWordState
      FiniteDependentWordPadding.WordState extendedProfileStateBound
    rw [Fintype.card_fin, Fintype.card_fun, Fintype.card_fin]
    positivity
  have hdummy0 : ∀ a, 0 ≤ dummyProb a := by
    intro a
    unfold dummyProb
    positivity
  have hdummySum : ∑ a, dummyProb a = 1 := by
    simp [dummyProb, Nat.ne_of_gt hStateCard]
  have hcolumnWhole : 0 ≤ Fintype.card Color * columnBound :=
    mul_nonneg (Nat.cast_nonneg _) hcolumnBound
  obtain ⟨choice, hchoicePos, hchoiceLoad⟩ :=
    FiniteCategoricalSelection.exists_supported_choice_rowLoad_lt_rowMean_add_deviation
      meanBound (Fintype.card Color * columnBound)
      hmeanBound hcolumnWhole hcolumnOne K hK hmeanK
      prob dummyProb use
      (G.paddedColorDependentExtendedProfileWordProbability_nonneg R
        hs hq hr0 hleft homega0 homega1)
      (G.sum_paddedColorDependentExtendedProfileWordProbability R omega)
      hdummy0 hdummySum
      (G.colorDependentWordCapacityUse_nonneg R RowAt atomUse hatom0)
      (G.colorDependentWordCapacityUse_le_one R RowAt atomUse hatom1)
      (G.colorDependentWordCapacity_rowMean_le
        R RowAt omega meanBound atomUse hmean)
      (G.sum_colorDependentWordCapacityUse_le_card_mul
        R RowAt atomUse columnBound hcolumn)
  have hdecode : ∀ v, ∃ word : G.ColorDependentExtendedProfileWord R v,
      G.encodeColorDependentExtendedProfileWord R v word = choice v ∧
        0 < G.colorDependentExtendedProfileWordMass R omega v word := by
    intro v
    exact G.exists_colorDependentExtendedProfileWord_of_padded_pos R
      hs hq hr0 hleft homega0 homega1 v (choice v) (hchoicePos v)
  let word : ∀ v, G.ColorDependentExtendedProfileWord R v :=
    fun v ↦ Classical.choose (hdecode v)
  have hcode : ∀ v,
      G.encodeColorDependentExtendedProfileWord R v (word v) = choice v := by
    intro v
    exact (Classical.choose_spec (hdecode v)).1
  have hchoiceDecode : ∀ v,
      G.decodeColorDependentExtendedProfileWord R v (choice v) = word v := by
    intro v
    rw [← hcode v, G.decode_encodeColorDependentExtendedProfileWord]
  refine ⟨word, ?_, ?_⟩
  · intro v
    exact (Classical.choose_spec (hdecode v)).2
  · intro row
    have hload := hchoiceLoad row
    change FiniteCategoricalSelection.rowLoad use row choice <
      FiniteCategoricalSelection.rowMean prob use row +
        FinitePartialResamplingNumerics.packingDeviation meanBound
          (Fintype.card Color * columnBound) at hload
    rw [G.colorDependentWordCapacity_rowMean_eq
      R RowAt omega atomUse row] at hload
    simpa [FiniteCategoricalSelection.rowLoad, use,
      colorDependentExtendedProfileWordCapacityUse, hchoiceDecode] using hload

end WeightedMultigraph

end

end WeightedEdgeColoring
