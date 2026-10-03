import WeightedEdgeColoring.MultigraphExtendedProfileBlockMeanPackingSelection
import WeightedEdgeColoring.MultigraphExtendedProfileBlockVarianceRows

/-!
# Simultaneous additive rows and block-variance rows

The finite PRA is run once.  Arbitrary additional rows (capacity rows and
first-moment complement rows in the application) are put beside the two
block-variance row families.  The conclusion exposes both their individual
mean-relative bounds and the resulting two-level variance estimate.

All analytic envelope and column estimates are explicit hypotheses here;
this file is the deterministic selection bridge.
-/

namespace WeightedEdgeColoring

open scoped BigOperators

noncomputable section

namespace WeightedMultigraph

universe u w

variable (G : WeightedMultigraph.{u})
variable {B k : ℕ}
variable {s β q r : ℝ} {hβ : 0 < β} {hr : 0 < r}
variable (R0 : ∀ v, G.BoundedProfileRealization
  (fun _e : G.StarEdge v ↦ (1 : ℝ) / ((B * k : ℕ) : ℝ))
    s β q r hβ hr)

variable {ExtraRow : Type w} [Fintype ExtraRow] [DecidableEq ExtraRow]

/-- Encode a dependent family of genuine selected block words in the common
padded block-state type. -/
def encodeExtendedProfileBlockSelection
    (selected : ∀ v (b : Fin B),
      Fin k → G.ExtendedProfileState R0 v) :
    (G.V × Fin B) → ExtendedProfilePackedBlockState k β q r :=
  fun src ↦ FiniteDependentWordPadding.encodePackedWord
    (fun v ↦ G.ExtendedProfileState R0 v) (Color := Fin k)
    (G.extendedProfileStateEncoding R0) src.1 (selected src.1 src.2)

/-- Rows supplied by the application together with the quadratic rows. -/
abbrev ExtendedProfileBlockCombinedRow (ExtraRow : Type w) :=
  ExtraRow ⊕ G.ExtendedProfileBlockVarianceRow
    (B := B) (k := k) (β := β) (q := q) (r := r)

def extendedProfileBlockCombinedUse
    (rho omega pairScale selfScale : ℝ)
    (extraUse : (G.V × Fin B) →
      ExtendedProfilePackedBlockState k β q r → ExtraRow → ℝ)
    (source : G.V × Fin B)
    (sourceCode : ExtendedProfilePackedBlockState k β q r)
    (row : G.ExtendedProfileBlockCombinedRow ExtraRow
      (B := B) (k := k) (β := β) (q := q) (r := r)) : ℝ :=
  match row with
  | Sum.inl extra => extraUse source sourceCode extra
  | Sum.inr variance =>
      G.scaledExtendedProfileBlockVarianceUse R0 rho omega
        pairScale selfScale source sourceCode variance

/-- One supported block selection simultaneously controls arbitrary extra
rows and the two conditioning levels of the quadratic statistic. -/
theorem exists_extendedProfileBlock_combined_rows
    (omega : ℝ)
    (hs : 0 ≤ s) (hq : 0 ≤ q) (hr0 : 0 ≤ r)
    (hleft : 0 ≤ 1 - s * (1 + q + r))
    (homega0 : 0 < omega) (homega1 : omega ≤ 1)
    (rho pairScale selfScale : ℝ)
    (hpair : 0 < pairScale) (hself : 0 < selfScale)
    (extraUse : (G.V × Fin B) →
      ExtendedProfilePackedBlockState k β q r → ExtraRow → ℝ)
    (R C : ℝ) (hR : 0 < R) (hC : 0 ≤ C) (hC1 : 1 ≤ C)
    (K : ℕ) (hK : 0 < K) (hRK : R ≤ K)
    (dummyProb : ExtendedProfilePackedBlockState k β q r → ℝ)
    (hdummy0 : ∀ a, 0 ≤ dummyProb a)
    (hdummySum : ∑ a, dummyProb a = 1)
    (huse0 : ∀ src a row,
      0 ≤ G.extendedProfileBlockCombinedUse R0 rho omega
        pairScale selfScale extraUse src a row)
    (huse1 : ∀ src a row,
      G.extendedProfileBlockCombinedUse R0 rho omega
        pairScale selfScale extraUse src a row ≤ 1)
    (hmean : ∀ row,
      FiniteCategoricalSelection.rowMean
          (fun src a ↦
            G.paddedExtendedProfileBlockProbability R0 omega src.1 a)
          (G.extendedProfileBlockCombinedUse R0 rho omega
            pairScale selfScale extraUse) row ≤ R)
    (hcolumn : ∀ src a,
      ∑ row,
        G.extendedProfileBlockCombinedUse R0 rho omega
          pairScale selfScale extraUse src a row ≤ C) :
    ∃ selected : ∀ v (b : Fin B),
        Fin k → G.ExtendedProfileState R0 v,
      (∀ v b,
        0 < G.extendedProfileBlockMass R0 omega v (selected v b)) ∧
      (∀ row : ExtraRow,
        FiniteCategoricalSelection.rowLoad extraUse row
            (G.encodeExtendedProfileBlockSelection R0 selected) <
          FiniteCategoricalSelection.rowMean
            (fun src a ↦
              G.paddedExtendedProfileBlockProbability R0 omega src.1 a)
            extraUse row +
              FinitePartialResamplingNumerics.packingDeviation R C) ∧
      ∀ v,
        G.selectedTotalRawExtendedProfileBlockVariance R0 rho omega
            (G.encodeExtendedProfileBlockSelection R0 selected) v ≤
          G.meanTotalExtendedProfileBlockVariance R0 rho omega v +
            selfScale *
              FinitePartialResamplingNumerics.packingDeviation R C +
            B * pairScale *
              FinitePartialResamplingNumerics.packingDeviation R C := by
  let combinedUse := G.extendedProfileBlockCombinedUse R0 rho omega
    pairScale selfScale extraUse
  obtain ⟨selected, hselected, hrows⟩ :=
    G.exists_extendedProfileBlock_rowLoad_lt_rowMean_add_deviation R0 omega
      hs hq hr0 hleft homega0 homega1 combinedUse
      R C hR hC hC1 K hK hRK dummyProb hdummy0 hdummySum
      huse0 huse1 hmean hcolumn
  let choice := G.encodeExtendedProfileBlockSelection R0 selected
  have hextra : ∀ row : ExtraRow,
      FiniteCategoricalSelection.rowLoad extraUse row choice <
        FiniteCategoricalSelection.rowMean
          (fun src a ↦
            G.paddedExtendedProfileBlockProbability R0 omega src.1 a)
          extraUse row +
            FinitePartialResamplingNumerics.packingDeviation R C := by
    intro row
    simpa [combinedUse, extendedProfileBlockCombinedUse, choice] using
      hrows (Sum.inl row)
  have hvariance : ∀ row : G.ExtendedProfileBlockVarianceRow
      (B := B) (k := k) (β := β) (q := q) (r := r),
      FiniteCategoricalSelection.rowLoad
          (G.scaledExtendedProfileBlockVarianceUse R0 rho omega
            pairScale selfScale) row choice ≤
        FiniteCategoricalSelection.rowMean
          (fun src a ↦
            G.paddedExtendedProfileBlockProbability R0 omega src.1 a)
          (G.scaledExtendedProfileBlockVarianceUse R0 rho omega
            pairScale selfScale) row +
              FinitePartialResamplingNumerics.packingDeviation R C := by
    intro row
    have h := (hrows (Sum.inr row)).le
    simpa [combinedUse, extendedProfileBlockCombinedUse, choice] using h
  refine ⟨selected, hselected, ?_, ?_⟩
  · simpa [choice] using hextra
  · simpa [choice] using
      (G.selectedTotalRawBlockVariance_le_of_rowBounds R0 rho omega
        pairScale selfScale
        (FinitePartialResamplingNumerics.packingDeviation R C)
        hpair hself choice hvariance)

end WeightedMultigraph

end

end WeightedEdgeColoring
