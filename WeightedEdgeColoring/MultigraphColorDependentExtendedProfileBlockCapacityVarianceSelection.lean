import WeightedEdgeColoring.MultigraphColorDependentExtendedProfileBlockVarianceBounds
import WeightedEdgeColoring.MultigraphColorDependentExtendedProfileBlockCapacityBounds

/-!
# Simultaneous colour-dependent capacity and block-square selection

This module plugs the concrete weighted-square rows into the fixed-block
selector.  Analytic scale bounds remain individual inequalities, so later
parameter files can discharge them with the sharp diffuse-proposal
estimates without changing the selection proof.
-/

namespace WeightedEdgeColoring

open scoped BigOperators

noncomputable section

namespace WeightedMultigraph

universe u

variable (G : WeightedMultigraph.{u})
variable {B k n : ℕ}
variable {s β q r : ℝ} {hβ : 0 < β} {hr : 0 < r}
variable (proposal : G.E → (Fin B × Fin k) → ℝ)
variable (R : ∀ v c, G.BoundedProfileRealization
  (fun e : G.StarEdge v ↦ proposal e.1 c) s β q r hβ hr)

local instance : ∀ p : Prop, Decidable p := Classical.propDecidable

def colorDependentBlockSparseVarianceColumnBound
    (n k : ℕ) (β q r : ℝ) : ℝ :=
  (extendedProfileStateBound β q r : ℝ) ^ k * n + 1

def colorDependentBlockCombinedColumnBound
    (n k : ℕ) (β q r : ℝ) : ℝ :=
  (k : ℝ) * colorDependentCandidatePerColorColumnBound n β q r +
    colorDependentBlockSparseVarianceColumnBound n k β q r

def colorDependentBlockSharpVarianceMean
    (n : ℕ) (rho s omega β q r C0 : ℝ) : ℝ :=
  colorDependentBlockOptionUpper n 1 rho s omega β q r C0 *
    (rho * s * n)

/-- Sparse support cap for the two variance-row levels. -/
def colorDependentBlockVarianceCap
    (source : G.V × Fin B)
    (row : G.ColorDependentBlockVarianceRow
      (B := B) (k := k) (β := β) (q := q) (r := r)) : ℝ :=
  match row with
  | Sum.inl candidate =>
      if source.2 = candidate.2.1 ∧
          ∃ e, G.ColorDependentCandidateEdgeMatches
            candidate.1 source.1 e then 1 else 0
  | Sum.inr v => if source.1 = v then 1 else 0

theorem colorDependentBlockVarianceCap_nonneg
    (source : G.V × Fin B)
  (row : G.ColorDependentBlockVarianceRow
      (B := B) (k := k) (β := β) (q := q) (r := r)) :
    0 ≤ G.colorDependentBlockVarianceCap source row := by
  rcases row with row | v <;>
    simp only [colorDependentBlockVarianceCap] <;>
    split_ifs <;> norm_num

theorem colorDependentBlockVarianceCap_le_one
    (source : G.V × Fin B)
  (row : G.ColorDependentBlockVarianceRow
      (B := B) (k := k) (β := β) (q := q) (r := r)) :
    G.colorDependentBlockVarianceCap source row ≤ 1 := by
  rcases row with row | v <;>
    simp only [colorDependentBlockVarianceCap] <;>
    split_ifs <;> norm_num

/-- A simple explicit column bound for the sparse variance caps.  The later
sharp bound may replace the candidate-row cardinal by its incidence count;
this finite bound is already polynomial when the block size is fixed. -/
theorem sum_colorDependentBlockVarianceCap_le_card
    (source : G.V × Fin B) :
    (∑ row : G.ColorDependentBlockVarianceRow
        (B := B) (k := k) (β := β) (q := q) (r := r),
      G.colorDependentBlockVarianceCap source row) ≤
      Fintype.card (G.ColorDependentBlockVarianceRow
        (B := B) (k := k) (β := β) (q := q) (r := r)) := by
  calc
    _ ≤ ∑ _row : G.ColorDependentBlockVarianceRow
        (B := B) (k := k) (β := β) (q := q) (r := r), (1 : ℝ) :=
      Finset.sum_le_sum fun row _hrow ↦
        G.colorDependentBlockVarianceCap_le_one source row
    _ = _ := by simp

/-- Concrete simultaneous selector.  Besides exact-mean capacity control it
returns the weighted whole-edge square needed for clipping and the squared
signed star deficit obtained from it by weighted Cauchy--Schwarz. -/
theorem exists_colorDependentExtendedProfileBlock_capacity_and_variance
    {L : ℕ} (hL : 0 < L) (hmult : G.PairMultiplicityAtMost L)
    (hB : 0 < B) (hn : 0 < n)
    (hs : 0 ≤ s) (hspos : 0 < s) (hq : 0 ≤ q) (hr0 : 0 ≤ r)
    (hleft : 0 ≤ 1 - s * (1 + q + r))
    (omega : ℝ) (homega0 : 0 < omega) (homega1 : omega < 1)
    (rho C0 : ℝ) (hrho : 0 < rho) (hC0 : 0 < C0)
    (hproposal : ∀ e c, proposal e c ≤ C0 / (n : ℝ))
    (hstar : ∀ v, G.starWeight v ≤ n)
    (pairScale selfScale varianceMeanRaw meanBound columnBound : ℝ)
    (hpair : 0 < pairScale) (hself : 0 < selfScale)
    (hmeanBound : 0 < meanBound) (hcolumnBound : 0 ≤ columnBound)
    (hcolumnOne : 1 ≤ columnBound)
    (K : ℕ) (hK : 0 < K) (hmeanK : meanBound ≤ K)
    (dummyProb : G.ColorDependentExtendedProfilePackedBlockState
      (k := k) (β := β) (q := q) (r := r) → ℝ)
    (hdummy0 : ∀ a, 0 ≤ dummyProb a)
    (hdummySum : ∑ a, dummyProb a = 1)
    (hcapacityMeanBound :
      (n : ℝ) * (rho / (1 - omega)) /
          ((L : ℝ) * colorDependentCandidateCapacityScale
            rho s omega β q r C0) ≤ meanBound)
    (hvariance0 : ∀ src a row,
      0 ≤ G.scaledColorDependentBlockVarianceUse proposal R rho omega
        pairScale selfScale src a row)
    (hvariance1 : ∀ src a row,
      G.scaledColorDependentBlockVarianceUse proposal R rho omega
        pairScale selfScale src a row ≤ 1)
    (hvarianceMeanUpper : ∀ row,
      FiniteCategoricalSelection.rowMean
        (G.paddedColorDependentExtendedProfileBlockProbability proposal R omega)
        (G.scaledColorDependentBlockVarianceUse proposal R rho omega
          pairScale selfScale) row ≤ meanBound)
    (varianceColumnBound : ℝ)
    (hvarianceColumn : ∀ src a,
      (∑ row, G.scaledColorDependentBlockVarianceUse
        proposal R rho omega pairScale selfScale src a row) ≤
          varianceColumnBound)
    (hcombinedColumn :
      k * colorDependentCandidatePerColorColumnBound n β q r +
        varianceColumnBound ≤ columnBound)
    (hmeanTotal : ∀ v,
      G.meanTotalColorDependentBlockVariance proposal R rho omega v ≤
        varianceMeanRaw) :
    ∃ selected : ∀ v (b : Fin B) (i : Fin k),
        G.ColorDependentExtendedProfileState R v (b, i),
      (∀ v b,
        0 < G.paddedColorDependentExtendedProfileBlockProbability
          proposal R omega (v, b)
          (G.encodeColorDependentExtendedProfileBlock
            proposal R v b (selected v b))) ∧
      (∀ row : G.ColorDependentExtendedProfileCapacityRow
          (G.ColorDependentCandidateRowAt R),
        FiniteCategoricalSelection.rowLoad
          (G.colorDependentBlockCandidateUse proposal R n
            ((L : ℝ) * colorDependentCandidateCapacityScale
              rho s omega β q r C0) rho omega) row
          (fun src ↦ G.encodeColorDependentExtendedProfileBlock
            proposal R src.1 src.2 (selected src.1 src.2)) <
        FiniteCategoricalSelection.rowMean
          (G.paddedColorDependentExtendedProfileBlockProbability proposal R omega)
          (G.colorDependentBlockCandidateUse proposal R n
            ((L : ℝ) * colorDependentCandidateCapacityScale
              rho s omega β q r C0) rho omega) row +
          FinitePartialResamplingNumerics.packingDeviation
            meanBound columnBound) ∧
      let choice := fun src ↦ G.encodeColorDependentExtendedProfileBlock
        proposal R src.1 src.2 (selected src.1 src.2)
      (∀ v,
        (∑ e : G.StarEdge v, G.weight e.1 *
          (G.selectedColorDependentTotalOptionMass
              proposal R rho omega choice e.1 -
            G.colorDependentTotalTarget proposal rho s e.1) ^ 2) ≤
          B * (varianceMeanRaw + selfScale *
              FinitePartialResamplingNumerics.packingDeviation
                meanBound columnBound +
            B * pairScale *
              FinitePartialResamplingNumerics.packingDeviation
                meanBound columnBound)) ∧
      ∀ v,
        (∑ e : G.StarEdge v, G.weight e.1 *
          (G.colorDependentTotalTarget proposal rho s e.1 -
            G.selectedColorDependentTotalOptionMass
              proposal R rho omega choice e.1)) ^ 2 ≤
          G.starWeight v *
            (B * (varianceMeanRaw + selfScale *
                FinitePartialResamplingNumerics.packingDeviation
                  meanBound columnBound +
              B * pairScale *
                FinitePartialResamplingNumerics.packingDeviation
                  meanBound columnBound)) := by
  let scale := (L : ℝ) *
    colorDependentCandidateCapacityScale rho s omega β q r C0
  let varianceUse := G.scaledColorDependentBlockVarianceUse
    proposal R rho omega pairScale selfScale
  have hcapColumn : ∀ src a,
      (∑ row, G.colorDependentBlockCandidateUse proposal R n scale
          rho omega src a row) + ∑ row,
            varianceUse src a row ≤
        columnBound := by
    intro src a
    exact (add_le_add
      (G.sum_colorDependentBlockCandidateUse_le_column proposal R
        hL hn hspos hq hr0 hleft homega0 homega1.le hrho hC0
          hproposal hstar src a)
      (hvarianceColumn src a)).trans
        hcombinedColumn
  obtain ⟨selected, hsupport, hcapacity, hvariance⟩ :=
    G.exists_colorDependentExtendedProfileBlock_capacity_and_upper
      proposal R hs hq hr0 hleft omega homega0 homega1.le scale rho
      varianceUse meanBound columnBound hmeanBound
      hcolumnBound hcolumnOne K hK hmeanK dummyProb hdummy0 hdummySum
      (fun v c z row ↦
        G.scaledColorDependentCandidateAtomUse_nonneg
          proposal R hs hq hr0 hleft homega0 homega1.le hrho.le
            (mul_nonneg (Nat.cast_nonneg L)
              (colorDependentCandidateCapacityScale_nonneg
                (C0 := C0) hrho.le hs hC0.le homega0.le)) v c z row)
      (fun v c z row ↦
        G.scaledColorDependentCandidateAtomUse_le_one
          proposal R hL hmult hn hspos hq hr0 hleft homega0 homega1.le hrho hC0
            hproposal v c z row)
      (fun row ↦ by
        exact (G.scaledColorDependentCandidateAtomMean_le_one_sub_omega
          proposal R n scale hs hq hr0 hleft homega0 homega1
          hrho.le (mul_pos (by exact_mod_cast hL)
            (colorDependentCandidateCapacityScale_pos
              (C0 := C0) hrho hspos hC0 homega0)) row.1 row.2).trans
          hcapacityMeanBound)
      hvariance0 hvariance1 hvarianceMeanUpper hcapColumn
  let choice := fun (src : G.V × Fin B) ↦
    G.encodeColorDependentExtendedProfileBlock
    proposal R src.1 src.2 (selected src.1 src.2)
  have hrows : ∀ row,
      FiniteCategoricalSelection.rowLoad varianceUse row choice ≤
        FiniteCategoricalSelection.rowMean
          (G.paddedColorDependentExtendedProfileBlockProbability proposal R omega)
          varianceUse row +
            FinitePartialResamplingNumerics.packingDeviation
              meanBound columnBound := by
    intro row
    exact (hvariance row).le
  have htotal : ∀ v,
      G.selectedTotalRawColorDependentBlockVariance
          proposal R rho omega choice v ≤
        varianceMeanRaw + selfScale *
            FinitePartialResamplingNumerics.packingDeviation
              meanBound columnBound +
          B * pairScale *
            FinitePartialResamplingNumerics.packingDeviation
              meanBound columnBound := by
    intro v
    exact (G.selectedTotalRawColorDependentBlockVariance_le_of_rowBounds
      proposal R rho omega pairScale selfScale
      (FinitePartialResamplingNumerics.packingDeviation meanBound columnBound)
      hpair hself choice hrows v).trans (by gcongr; exact hmeanTotal v)
  refine ⟨selected, hsupport, ?_, ?_, ?_⟩
  · intro row
    have hcap := hcapacity row
    rw [← G.colorDependentBlockCandidate_rowMean_eq
      proposal R omega scale rho row] at hcap
    simpa [choice, scale] using hcap
  · intro v
    exact (G.selectedColorDependentTotalOptionMass_weightedSquare_le
      proposal R choice rho omega v).trans
        (mul_le_mul_of_nonneg_left (htotal v) (Nat.cast_nonneg B))
  · intro v
    have hstar0 : 0 ≤ G.starWeight v := Finset.sum_nonneg fun e _he ↦
      G.weight_nonneg e.1
    have hcauchy := colorDependentWeightedSignedDeficit_sq_le
      (fun e : G.StarEdge v ↦ G.weight e.1)
      (fun e : G.StarEdge v ↦
        G.colorDependentTotalTarget proposal rho s e.1 -
          G.selectedColorDependentTotalOptionMass
            proposal R rho omega choice e.1)
      (fun e ↦ G.weight_nonneg e.1)
    have hquad := G.selectedColorDependentTotalOptionMass_weightedSquare_le
      proposal R choice rho omega v
    have hsign : (∑ e : G.StarEdge v, G.weight e.1 *
        (G.colorDependentTotalTarget proposal rho s e.1 -
          G.selectedColorDependentTotalOptionMass
            proposal R rho omega choice e.1) ^ 2) =
      (∑ e : G.StarEdge v, G.weight e.1 *
        (G.selectedColorDependentTotalOptionMass
            proposal R rho omega choice e.1 -
          G.colorDependentTotalTarget proposal rho s e.1) ^ 2) := by
      apply Finset.sum_congr rfl
      intro e _he
      congr 1
      ring
    rw [hsign] at hcauchy
    exact hcauchy.trans (mul_le_mul_of_nonneg_left
      (hquad.trans (mul_le_mul_of_nonneg_left (htotal v)
        (Nat.cast_nonneg B))) hstar0)

/-- Closed block selector with the natural variance normalizations.  The
only remaining scalar input is the capacity-row mean inequality.  All
variance means, pointwise envelopes, and sparse columns are discharged
here; in particular, the column bound is independent of `Fintype.card G.V`.
-/
theorem exists_colorDependentExtendedProfileBlock_capacity_and_variance_natural
    {L : ℕ} (hL : 0 < L) (hmult : G.PairMultiplicityAtMost L)
    (hB : 0 < B) (hk : 0 < k) (hn : 0 < n) (hBn : B ≤ n)
    (hs : 0 < s) (hq : 0 ≤ q) (hr0 : 0 ≤ r)
    (hleft : 0 ≤ 1 - s * (1 + q + r))
    (omega : ℝ) (homega0 : 0 < omega) (homega1 : omega < 1)
    (rho C0 : ℝ) (hrho : 0 < rho) (hC0 : 0 < C0)
    (hproposal0 : ∀ e c, 0 ≤ proposal e c)
    (hproposal : ∀ e c, proposal e c ≤ C0 / (n : ℝ))
    (hmass : ∀ e, ∑ c, proposal e c ≤ 1)
    (hstar : ∀ v, G.starWeight v ≤ n)
    (hcapacityMeanBound :
      (n : ℝ) * (rho / (1 - omega)) /
          ((L : ℝ) * colorDependentCandidateCapacityScale
            rho s omega β q r C0) ≤ n) :
    ∃ selected : ∀ v (b : Fin B) (i : Fin k),
        G.ColorDependentExtendedProfileState R v (b, i),
      (∀ v b,
        0 < G.paddedColorDependentExtendedProfileBlockProbability
          proposal R omega (v, b)
          (G.encodeColorDependentExtendedProfileBlock
            proposal R v b (selected v b))) ∧
      (∀ row : G.ColorDependentExtendedProfileCapacityRow
          (G.ColorDependentCandidateRowAt R),
        FiniteCategoricalSelection.rowLoad
          (G.colorDependentBlockCandidateUse proposal R n
            ((L : ℝ) * colorDependentCandidateCapacityScale
              rho s omega β q r C0) rho omega) row
          (fun src ↦ G.encodeColorDependentExtendedProfileBlock
            proposal R src.1 src.2 (selected src.1 src.2)) <
        FiniteCategoricalSelection.rowMean
          (G.paddedColorDependentExtendedProfileBlockProbability proposal R omega)
          (G.colorDependentBlockCandidateUse proposal R n
            ((L : ℝ) * colorDependentCandidateCapacityScale
              rho s omega β q r C0) rho omega) row +
          FinitePartialResamplingNumerics.packingDeviation
            n (colorDependentBlockCombinedColumnBound n k β q r)) ∧
      let choice := fun src ↦ G.encodeColorDependentExtendedProfileBlock
        proposal R src.1 src.2 (selected src.1 src.2)
      (∀ v,
        (∑ e : G.StarEdge v, G.weight e.1 *
          (G.selectedColorDependentTotalOptionMass
              proposal R rho omega choice e.1 -
            G.colorDependentTotalTarget proposal rho s e.1) ^ 2) ≤
          B * (colorDependentBlockSharpVarianceMean
                n rho s omega β q r C0 +
              ((L : ℝ) * colorDependentBlockVarianceSelfScale
                n k rho s omega β q r C0) *
                FinitePartialResamplingNumerics.packingDeviation
                  n (colorDependentBlockCombinedColumnBound n k β q r) +
            B * ((L : ℝ) * colorDependentBlockVariancePairScale
                n k rho s omega β q r C0) *
                FinitePartialResamplingNumerics.packingDeviation
                  n (colorDependentBlockCombinedColumnBound n k β q r))) ∧
      ∀ v,
        (∑ e : G.StarEdge v, G.weight e.1 *
          (G.colorDependentTotalTarget proposal rho s e.1 -
            G.selectedColorDependentTotalOptionMass
              proposal R rho omega choice e.1)) ^ 2 ≤
          G.starWeight v *
            (B * (colorDependentBlockSharpVarianceMean
                  n rho s omega β q r C0 +
                ((L : ℝ) * colorDependentBlockVarianceSelfScale
                  n k rho s omega β q r C0) *
                  FinitePartialResamplingNumerics.packingDeviation
                    n (colorDependentBlockCombinedColumnBound n k β q r) +
              B * ((L : ℝ) * colorDependentBlockVariancePairScale
                  n k rho s omega β q r C0) *
                  FinitePartialResamplingNumerics.packingDeviation
                    n (colorDependentBlockCombinedColumnBound n k β q r))) := by
  let pairScale := (L : ℝ) * colorDependentBlockVariancePairScale
    n k rho s omega β q r C0
  let selfScale := (L : ℝ) * colorDependentBlockVarianceSelfScale
    n k rho s omega β q r C0
  let varianceMeanRaw := colorDependentBlockSharpVarianceMean
    n rho s omega β q r C0
  let varianceColumnBound := colorDependentBlockSparseVarianceColumnBound
    n k β q r
  let columnBound := colorDependentBlockCombinedColumnBound n k β q r
  let State := G.ColorDependentExtendedProfilePackedBlockState
    (k := k) (β := β) (q := q) (r := r)
  let dummyProb : State → ℝ := fun _ ↦ 1 / Fintype.card State
  have hStateCard : 0 < Fintype.card State := by
    unfold State ColorDependentExtendedProfilePackedBlockState
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
  have hLreal : (0 : ℝ) < L := by exact_mod_cast hL
  have hLone : (1 : ℝ) ≤ L := by exact_mod_cast hL
  have hbasePair : 0 < colorDependentBlockVariancePairScale
      n k rho s omega β q r C0 :=
    colorDependentBlockVariancePairScale_pos hn hk hrho hs homega0 hC0
  have hbasePair_le : colorDependentBlockVariancePairScale
      n k rho s omega β q r C0 ≤
        (L : ℝ) * colorDependentBlockVariancePairScale
          n k rho s omega β q r C0 := by
    nlinarith [hbasePair.le]
  have hpair : 0 < pairScale := mul_pos hLreal
    hbasePair
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hself : 0 < selfScale := by
    unfold selfScale
    exact mul_pos hLreal (by
      unfold colorDependentBlockVarianceSelfScale
      exact mul_pos hnR
        (colorDependentBlockVariancePairScale_pos
          hn hk hrho hs homega0 hC0))
  have hperColumn0 : 0 ≤
      colorDependentCandidatePerColorColumnBound n β q r := by
    unfold colorDependentCandidatePerColorColumnBound
    positivity
  have hvarianceColumn0 : 0 ≤ varianceColumnBound := by
    unfold varianceColumnBound colorDependentBlockSparseVarianceColumnBound
    positivity
  have hcolumn0 : 0 ≤ columnBound := by
    unfold columnBound colorDependentBlockCombinedColumnBound
    positivity
  have hcolumnOne : 1 ≤ columnBound := by
    unfold columnBound colorDependentBlockCombinedColumnBound
      colorDependentBlockSparseVarianceColumnBound
    nlinarith [mul_nonneg (Nat.cast_nonneg k) hperColumn0,
      mul_nonneg (by positivity :
        0 ≤ (extendedProfileStateBound β q r : ℝ) ^ k)
        (Nat.cast_nonneg n)]
  have henvelopes := G.scaledColorDependentBlockVarianceUse_envelopes
    proposal R hs.le hq hr0 hleft homega0 homega1.le rho
      pairScale selfScale (n : ℝ) hpair hself
      (by
        simp only [selfScale, pairScale, colorDependentBlockVarianceSelfScale]
        ring_nf
        exact le_rfl)
      (fun src a row ↦ by
        exact G.rawColorDependentBlockVarianceCandidateUse_le_mul_pairScale
          proposal R hmult hn hs.le hq hr0 hleft homega0 homega1.le rho C0
          hrho.le hC0.le hproposal0 hproposal src a row)
      (fun row ↦ by
        have hbase := G.conditionalColorDependentBlockVariance_le_n_mul_pairScale
          proposal R hn hs.le hq hr0 hleft homega0 homega1.le rho C0
          hrho.le hC0.le hproposal0 hproposal hstar row
        exact hbase.trans (by
          change (n : ℝ) * colorDependentBlockVariancePairScale
              n k rho s omega β q r C0 ≤ (n : ℝ) * pairScale
          exact mul_le_mul_of_nonneg_left hbasePair_le hnR.le))
      (fun v ↦ by
        have hcoarse := G.meanTotalColorDependentBlockVariance_le proposal R
          hn hs.le hq hr0 hleft homega0 homega1.le rho C0 hrho.le hC0.le
          hproposal0 hproposal hstar v
        change G.meanTotalColorDependentBlockVariance
            proposal R rho omega v ≤
          (n : ℝ) * ((L : ℝ) * ((n : ℝ) *
            colorDependentBlockVariancePairScale
              n k rho s omega β q r C0))
        have hBnR : (B : ℝ) ≤ n := by exact_mod_cast hBn
        calc
          G.meanTotalColorDependentBlockVariance proposal R rho omega v ≤
              B * (n * colorDependentBlockVariancePairScale
                n k rho s omega β q r C0) := hcoarse
          _ ≤ n * (n * colorDependentBlockVariancePairScale
                n k rho s omega β q r C0) := by
            exact mul_le_mul_of_nonneg_right hBnR
              (mul_nonneg hnR.le hbasePair.le)
          _ ≤ (n : ℝ) * ((L : ℝ) * ((n : ℝ) *
                colorDependentBlockVariancePairScale
                  n k rho s omega β q r C0)) := by
            apply mul_le_mul_of_nonneg_left _ hnR.le
            calc
              (n : ℝ) * colorDependentBlockVariancePairScale
                  n k rho s omega β q r C0 =
                1 * ((n : ℝ) * colorDependentBlockVariancePairScale
                  n k rho s omega β q r C0) := by ring
              _ ≤ (L : ℝ) * ((n : ℝ) * colorDependentBlockVariancePairScale
                  n k rho s omega β q r C0) :=
                mul_le_mul_of_nonneg_right hLone
                  (mul_nonneg hnR.le hbasePair.le)
          _ = (n : ℝ) * ((L : ℝ) * ((n : ℝ) *
                colorDependentBlockVariancePairScale
                  n k rho s omega β q r C0)) := by rfl)
  have hvarianceColumn : ∀ src a,
      (∑ row, G.scaledColorDependentBlockVarianceUse
        proposal R rho omega pairScale selfScale src a row) ≤
          varianceColumnBound := by
    intro src a
    exact G.sum_scaledColorDependentBlockVarianceUse_mul_le_sparseColumn
      proposal R hL hn hk hs hq hr0 hleft homega0 homega1.le rho C0
      hrho hC0 hproposal0 hproposal hstar src a
  have hmeanTotal : ∀ v,
      G.meanTotalColorDependentBlockVariance proposal R rho omega v ≤
        varianceMeanRaw := by
    intro v
    exact G.meanTotalColorDependentBlockVariance_le_sharp proposal R
      hn hs.le hq hr0 hleft homega0 homega1.le rho C0 hrho.le hC0.le
      hproposal0 hproposal hmass hstar v
  have hcombined :
      k * colorDependentCandidatePerColorColumnBound n β q r +
        varianceColumnBound ≤ columnBound := by
    unfold varianceColumnBound columnBound
      colorDependentBlockCombinedColumnBound
    norm_num
  simpa [pairScale, selfScale, varianceMeanRaw, varianceColumnBound,
    columnBound] using
    G.exists_colorDependentExtendedProfileBlock_capacity_and_variance
      proposal R hL hmult hB hn hs.le hs hq hr0 hleft omega homega0 homega1
      rho C0 hrho hC0 hproposal hstar pairScale selfScale
      varianceMeanRaw (n : ℝ) columnBound hpair hself hnR hcolumn0
      hcolumnOne n hn le_rfl dummyProb hdummy0 hdummySum
      hcapacityMeanBound henvelopes.1 henvelopes.2.1 henvelopes.2.2
      varianceColumnBound hvarianceColumn hcombined hmeanTotal

end WeightedMultigraph

end

end WeightedEdgeColoring
