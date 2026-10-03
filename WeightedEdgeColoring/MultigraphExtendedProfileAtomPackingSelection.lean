import WeightedEdgeColoring.MultigraphExtendedProfileWordPadding
import WeightedEdgeColoring.FinitePartialResamplingPackingSelection
import WeightedEdgeColoring.FinitePartialResamplingNumericsBounds

/-!
# Packing selection with one profile state per vertex and color

The whole-edge application must keep the `n` color coordinates as separate
categorical sources.  Treating a complete color word as one source hides the
product structure needed by capture rows and gives exponentially many
candidate states.  Here the source type is `G.V × Fin n`, while every
vertex-dependent extended-profile state is padded into the common atom type
`Fin (extendedProfileStateBound beta q r)`.
-/

namespace WeightedEdgeColoring

open scoped BigOperators

noncomputable section

namespace WeightedMultigraph

universe u w

variable (G : WeightedMultigraph.{u})
variable {n : ℕ}
variable {s β q r : ℝ} {hβ : 0 < β} {hr : 0 < r}
variable (R0 : ∀ v, G.BoundedProfileRealization
  (fun _e : G.StarEdge v ↦ (1 : ℝ) / n) s β q r hβ hr)

/-- The smoothed one-coordinate law padded into the common atom type. -/
def paddedExtendedProfileStateProbability (omega : ℝ) (v : G.V)
    (a : Fin (extendedProfileStateBound β q r)) : ℝ :=
  ∑ z : G.ExtendedProfileState R0 v,
    if G.extendedProfileStateCode R0 v z = a then
      G.smoothedExtendedProfileProbability R0 omega v z else 0

theorem paddedExtendedProfileStateProbability_nonneg
    (hs : 0 ≤ s) (hq : 0 ≤ q) (hr0 : 0 ≤ r)
    (hleft : 0 ≤ 1 - s * (1 + q + r))
    (homega0 : 0 < omega) (homega1 : omega ≤ 1)
    (v : G.V) (a : Fin (extendedProfileStateBound β q r)) :
    0 ≤ G.paddedExtendedProfileStateProbability R0 omega v a := by
  apply Finset.sum_nonneg
  intro z _hz
  split
  · exact (G.smoothedExtendedProfileProbability_pos R0 hs hq hr0 hleft
      homega0 homega1 v z).le
  · exact le_rfl

theorem sum_paddedExtendedProfileStateProbability
    (omega : ℝ) (v : G.V) :
    ∑ a, G.paddedExtendedProfileStateProbability R0 omega v a = 1 := by
  classical
  unfold paddedExtendedProfileStateProbability
  rw [Finset.sum_comm]
  calc
    (∑ z : G.ExtendedProfileState R0 v,
        ∑ a, if G.extendedProfileStateCode R0 v z = a then
          G.smoothedExtendedProfileProbability R0 omega v z else 0) =
        ∑ z : G.ExtendedProfileState R0 v,
          G.smoothedExtendedProfileProbability R0 omega v z := by
      apply Finset.sum_congr rfl
      intro z _hz
      simp
    _ = 1 := G.sum_smoothedExtendedProfileProbability R0 omega v

/-- Positive padded mass certifies that the code names a genuine extended
profile state. -/
theorem exists_extendedProfileState_of_padded_pos
    (hs : 0 ≤ s) (hq : 0 ≤ q) (hr0 : 0 ≤ r)
    (hleft : 0 ≤ 1 - s * (1 + q + r))
    (homega0 : 0 < omega) (homega1 : omega ≤ 1)
    (v : G.V) (a : Fin (extendedProfileStateBound β q r))
    (ha : 0 < G.paddedExtendedProfileStateProbability R0 omega v a) :
    ∃ z : G.ExtendedProfileState R0 v,
      G.extendedProfileStateCode R0 v z = a ∧
        0 < G.smoothedExtendedProfileProbability R0 omega v z := by
  classical
  unfold paddedExtendedProfileStateProbability at ha
  have hterm0 : ∀ z : G.ExtendedProfileState R0 v,
      0 ≤ (if G.extendedProfileStateCode R0 v z = a then
        G.smoothedExtendedProfileProbability R0 omega v z else 0) := by
    intro z
    split
    · exact (G.smoothedExtendedProfileProbability_pos R0 hs hq hr0 hleft
        homega0 homega1 v z).le
    · exact le_rfl
  rcases (Finset.sum_pos_iff_of_nonneg
      (fun z _hz ↦ hterm0 z)).mp ha with ⟨z, _hz, hz⟩
  by_cases hcode : G.extendedProfileStateCode R0 v z = a
  · exact ⟨z, hcode, by simpa [hcode] using hz⟩
  · simp [hcode] at hz

variable {Row : Type w} [Fintype Row] [DecidableEq Row]

/-- Select one genuine extended-profile atom independently for every
vertex--color source, subject to arbitrary additive packing rows. -/
theorem exists_extendedProfileAtom_rowLoad_lt_packing
    (omega : ℝ)
    (hs : 0 ≤ s) (hq : 0 ≤ q) (hr0 : 0 ≤ r)
    (hleft : 0 ≤ 1 - s * (1 + q + r))
    (homega0 : 0 < omega) (homega1 : omega ≤ 1)
    (use : (G.V × Fin n) → Fin (extendedProfileStateBound β q r) →
      Row → ℝ)
    (meanBound columnBound : ℝ)
    (hmeanBound : 0 < meanBound) (hcolumnBound : 0 ≤ columnBound)
    (huse0 : ∀ src a row, 0 ≤ use src a row)
    (huse1 : ∀ src a row, use src a row ≤ 1)
    (hmean : ∀ row,
      FiniteCategoricalSelection.rowMean
          (fun src a ↦
            G.paddedExtendedProfileStateProbability R0 omega src.1 a)
          use row ≤ meanBound)
    (hcolumn : ∀ src a, ∑ row, use src a row ≤ columnBound) :
    ∃ selected : ∀ v (c : Fin n), G.ExtendedProfileState R0 v,
      (∀ v c,
        0 < G.smoothedExtendedProfileProbability R0 omega v
          (selected v c)) ∧
      ∀ row,
        (∑ src : G.V × Fin n,
          use src (G.extendedProfileStateCode R0 src.1
            (selected src.1 src.2)) row) <
          meanBound +
            FinitePartialResamplingNumerics.packingDeviation
              meanBound columnBound := by
  let prob : (G.V × Fin n) →
      Fin (extendedProfileStateBound β q r) → ℝ :=
    fun src a ↦ G.paddedExtendedProfileStateProbability R0 omega src.1 a
  obtain ⟨choice, hchoicePos, hchoiceLoad⟩ :=
    FiniteCategoricalSelection.exists_supported_choice_rowLoad_lt_packingThreshold
      meanBound columnBound hmeanBound hcolumnBound prob use
      (fun src a ↦ G.paddedExtendedProfileStateProbability_nonneg R0
        hs hq hr0 hleft homega0 homega1 src.1 a)
      (fun src ↦ G.sum_paddedExtendedProfileStateProbability R0 omega src.1)
      huse0 huse1 hmean hcolumn
  have hdecode : ∀ src : G.V × Fin n,
      ∃ z : G.ExtendedProfileState R0 src.1,
        G.extendedProfileStateCode R0 src.1 z = choice src ∧
          0 < G.smoothedExtendedProfileProbability R0 omega src.1 z := by
    intro src
    exact G.exists_extendedProfileState_of_padded_pos R0 hs hq hr0 hleft
      homega0 homega1 src.1 (choice src) (hchoicePos src)
  let selected : ∀ v (c : Fin n), G.ExtendedProfileState R0 v :=
    fun v c ↦ Classical.choose (hdecode (v, c))
  have hcode : ∀ src : G.V × Fin n,
      G.extendedProfileStateCode R0 src.1
          (selected src.1 src.2) = choice src := by
    intro src
    exact (Classical.choose_spec (hdecode src)).1
  refine ⟨selected, ?_, ?_⟩
  · intro v c
    exact (Classical.choose_spec (hdecode (v, c))).2
  · intro row
    have hload := hchoiceLoad row
    have hthreshold :=
      FinitePartialResamplingNumerics.packingThreshold_le_base_add_deviation
        hmeanBound hcolumnBound
    calc
      (∑ src : G.V × Fin n,
          use src (G.extendedProfileStateCode R0 src.1
            (selected src.1 src.2)) row) =
          FiniteCategoricalSelection.rowLoad use row choice := by
        simp only [FiniteCategoricalSelection.rowLoad, hcode]
      _ < FinitePartialResamplingNumerics.packingThreshold
          meanBound columnBound := hload
      _ ≤ meanBound +
          FinitePartialResamplingNumerics.packingDeviation
            meanBound columnBound := hthreshold

end WeightedMultigraph

end

end WeightedEdgeColoring
