import WeightedEdgeColoring.ExtendedProfileReservoirCandidateCapacityBounds
import WeightedEdgeColoring.ExtendedProfileBlockCapacityVarianceSelection

/-!
# Reservoir-sensitive simultaneous block selection

The simultaneous capacity and variance selector is kept in its mean-relative
form.  Consequently, after the selected center state is substituted into a
tiny row, its own reservoir size remains in the final capacity bound.
-/

namespace WeightedEdgeColoring

open scoped BigOperators

noncomputable section

namespace WeightedSimpleGraph

universe u

variable (G : WeightedSimpleGraph.{u})
variable {B k : ℕ}
variable {s β q r : ℝ} {hβ : 0 < β} {hr : 0 < r}
variable (R0 : ∀ v, G.BoundedProfileRealization
  (fun _e : G.StarEdge v ↦ (1 : ℝ) / ((B * k : ℕ) : ℝ))
    s β q r hβ hr)

@[simp] theorem decoded_encodeExtendedProfileBlockSelection
    (selected : ∀ v (b : Fin B),
      Fin k → G.ExtendedProfileState R0 v)
    (v : G.V) (c : Fin (B * k)) :
    G.decodedExtendedProfileBlockSelection R0
        (G.encodeExtendedProfileBlockSelection R0 selected) v c =
      selected v (extendedProfileColorBlock c)
        (extendedProfileColorPosition c) := by
  simp [decodedExtendedProfileBlockSelection,
    encodeExtendedProfileBlockSelection]

/-- The simultaneous capacity-and-variance selector before replacing each
capacity-row mean by one common upper bound. -/
theorem exists_extendedProfileBlock_capacity_and_variance_meanRelative
    (hB : 0 < B) (hk : 0 < k) (hn : 0 < B * k)
    (hs : 0 ≤ s) (hspos : 0 < s)
    (hq : 0 ≤ q) (hr0 : 0 ≤ r)
    (hleft : 0 ≤ 1 - s * (1 + q + r))
    (omega : ℝ) (homega0 : 0 < omega) (homega1 : omega ≤ 1)
    (rho : ℝ) (hrho : 0 < rho)
    (hpack : G.LocallyPacksInto (B * k))
    (K : ℕ) (hK : 0 < K)
    (hRK : extendedProfileBlockCombinedMeanBound
      rho s omega β q r B k ≤ K)
    (dummyProb : ExtendedProfilePackedBlockState k β q r → ℝ)
    (hdummy0 : ∀ a, 0 ≤ dummyProb a)
    (hdummySum : ∑ a, dummyProb a = 1) :
    ∃ selected : ∀ v (b : Fin B),
        Fin k → G.ExtendedProfileState R0 v,
      (∀ v b,
        0 < G.extendedProfileBlockMass R0 omega v (selected v b)) ∧
      (∀ row : G.ExtendedProfileCandidateCapacityRow R0
          (n := B * k) (β := β) (q := q) (r := r),
        FiniteCategoricalSelection.rowLoad
            (G.scaledBlockExtendedProfileCandidateCapacityUse R0 rho omega
              (extendedProfileCandidateCapacityScale rho s omega β q r))
            row (G.encodeExtendedProfileBlockSelection R0 selected) <
          FiniteCategoricalSelection.rowMean
              (fun source a ↦
                G.paddedExtendedProfileBlockProbability
                  R0 omega source.1 a)
              (G.scaledBlockExtendedProfileCandidateCapacityUse R0 rho omega
                (extendedProfileCandidateCapacityScale rho s omega β q r))
              row +
            extendedProfileBlockCombinedDeviation
              rho s omega β q r B k) ∧
      ∀ v,
        G.selectedTotalRawExtendedProfileBlockVariance R0 rho omega
            (G.encodeExtendedProfileBlockSelection R0 selected) v ≤
          G.meanTotalExtendedProfileBlockVariance R0 rho omega v +
            extendedProfileBlockVarianceSelfScale
                rho s omega β q r B k *
              extendedProfileBlockCombinedDeviation
                rho s omega β q r B k +
            B * extendedProfileBlockVariancePairScale
                rho s omega β q r B k *
              extendedProfileBlockCombinedDeviation
                rho s omega β q r B k := by
  let capScale := extendedProfileCandidateCapacityScale rho s omega β q r
  let pairScale := extendedProfileBlockVariancePairScale
    rho s omega β q r B k
  let selfScale := extendedProfileBlockVarianceSelfScale
    rho s omega β q r B k
  let R := extendedProfileBlockCombinedMeanBound rho s omega β q r B k
  let C := extendedProfileBlockCombinedColumnBound B k β q r
  let capUse := G.scaledBlockExtendedProfileCandidateCapacityUse
    R0 rho omega capScale
  have hcapScale : 0 < capScale :=
    extendedProfileCandidateCapacityScale_pos
      (omega := omega) (β := β) (q := q) (r := r)
      hrho hspos homega0
  have hpair : 0 < pairScale :=
    extendedProfileBlockVariancePairScale_pos hB hrho hspos
  have hself : 0 < selfScale :=
    extendedProfileBlockVarianceSelfScale_pos hB hk hrho hspos
  have hnreal : 0 < (((B * k : ℕ) : ℝ)) := by
    exact_mod_cast hn
  have hkappa : 0 < extendedProfileSmoothingKappa omega β q r :=
    extendedProfileSmoothingKappa_pos
      (β := β) (q := q) (r := r) homega0 homega1
  have hR : 0 < R := by
    unfold R extendedProfileBlockCombinedMeanBound
    positivity
  have hC : 0 ≤ C := by
    unfold C extendedProfileBlockCombinedColumnBound
      extendedProfileCandidateCapacityColumnBound
      extendedProfileBlockVarianceColumnBound
    positivity
  have hC1 : 1 ≤ C := by
    have hcapacity : 0 ≤ (k : ℝ) *
        extendedProfileCandidateCapacityColumnBound (B * k) β q r := by
      unfold extendedProfileCandidateCapacityColumnBound
      positivity
    have hvariance : 0 ≤
        (extendedProfileStateBound β q r : ℝ) ^ k *
          ((B : ℝ) * (k : ℝ)) := by
      positivity
    unfold C extendedProfileBlockCombinedColumnBound
      extendedProfileBlockVarianceColumnBound
    linarith
  have hcombined0 : ∀ source a row,
      0 ≤ G.extendedProfileBlockCombinedUse R0 rho omega
        pairScale selfScale capUse source a row := by
    intro source a row
    rcases row with capacity | variance
    · exact G.scaledBlockCandidateCapacityUse_nonneg R0
        hn hs hq hr0 hleft homega0 homega1 hrho.le hcapScale.le
        source a capacity
    · exact G.scaledExtendedProfileBlockVarianceUse_nonneg R0
        hB hk hs hspos hq hr0 hleft homega0 homega1 rho hrho
        source a variance
  have hcombined1 : ∀ source a row,
      G.extendedProfileBlockCombinedUse R0 rho omega
        pairScale selfScale capUse source a row ≤ 1 := by
    intro source a row
    rcases row with capacity | variance
    · exact G.scaledBlockCandidateCapacityUse_le_one R0
        hn hs hq hr0 hleft homega0 homega1 hrho hspos source a capacity
    · exact G.scaledExtendedProfileBlockVarianceUse_le_one R0
        hB hk hn hs hspos hq hr0 hleft homega0 homega1 rho hrho hpack
        source a variance
  have hcombinedMean : ∀ row,
      FiniteCategoricalSelection.rowMean
          (fun source a ↦
            G.paddedExtendedProfileBlockProbability R0 omega source.1 a)
          (G.extendedProfileBlockCombinedUse R0 rho omega
            pairScale selfScale capUse) row ≤ R := by
    intro row
    rcases row with capacity | variance
    · change FiniteCategoricalSelection.rowMean
          (fun source a ↦
            G.paddedExtendedProfileBlockProbability R0 omega source.1 a)
          capUse capacity ≤ R
      have hcap := G.rowMean_scaledBlockCandidateCapacityUse_le R0
        hn hs hq hr0 hleft homega0 homega1 hrho hspos capacity
      unfold R extendedProfileBlockCombinedMeanBound
      exact hcap.trans (le_add_of_nonneg_left (by positivity))
    · change FiniteCategoricalSelection.rowMean
          (fun source a ↦
            G.paddedExtendedProfileBlockProbability R0 omega source.1 a)
          (G.scaledExtendedProfileBlockVarianceUse R0 rho omega
            pairScale selfScale) variance ≤ R
      have hvar := G.rowMean_scaledExtendedProfileBlockVarianceUse_le_n R0
        hB hk hn hs hspos hq hr0 hleft homega0 homega1 rho hrho hpack
        variance
      have hcapMean0 : 0 ≤ ((B * k : ℕ) : ℝ) * rho /
          (extendedProfileCandidateCapacityScale rho s omega β q r *
            extendedProfileSmoothingKappa omega β q r) := by
        positivity
      unfold R extendedProfileBlockCombinedMeanBound
      calc
        FiniteCategoricalSelection.rowMean
            (fun source a ↦
              G.paddedExtendedProfileBlockProbability R0 omega source.1 a)
            (G.scaledExtendedProfileBlockVarianceUse R0 rho omega
              pairScale selfScale) variance ≤ ((B * k : ℕ) : ℝ) := by
          simpa only [Nat.cast_mul] using hvar
        _ ≤ ((B * k : ℕ) : ℝ) +
            ((B * k : ℕ) : ℝ) * rho /
              (extendedProfileCandidateCapacityScale rho s omega β q r *
                extendedProfileSmoothingKappa omega β q r) :=
          le_add_of_nonneg_right hcapMean0
  have hcombinedColumn : ∀ source a,
      ∑ row,
        G.extendedProfileBlockCombinedUse R0 rho omega
          pairScale selfScale capUse source a row ≤ C := by
    intro source a
    rw [Fintype.sum_sum_type]
    apply add_le_add
    · exact G.sum_scaledBlockCandidateCapacityUse_le_column R0
        hn hs hq hr0 hleft homega0 homega1 hrho hspos hpack source a
    · exact G.sum_scaledExtendedProfileBlockVarianceUse_le_column R0
        hB hk hn hs hspos hq hr0 hleft homega0 homega1 rho hrho hpack
        source a
  obtain ⟨selected, hselected, hcapacityRows, hvariance⟩ :=
    G.exists_extendedProfileBlock_combined_rows R0 omega
      hs hq hr0 hleft homega0 homega1 rho pairScale selfScale
      hpair hself capUse R C hR hC hC1 K hK hRK
      dummyProb hdummy0 hdummySum hcombined0 hcombined1
      hcombinedMean hcombinedColumn
  refine ⟨selected, hselected, ?_, ?_⟩
  · simpa [capUse, capScale, R, C,
      extendedProfileBlockCombinedDeviation] using hcapacityRows
  · simpa [pairScale, selfScale, R, C,
      extendedProfileBlockCombinedDeviation] using hvariance

/-- Simultaneous selection with the large-row bound retained and the sharp
selected-reservoir bound for every tiny row. -/
theorem exists_extendedProfileBlock_reservoir_capacity_and_variance
    (hB : 0 < B) (hk : 0 < k) (hn : 0 < B * k)
    (hs : 0 ≤ s) (hspos : 0 < s)
    (hq : 0 ≤ q) (hr0 : 0 ≤ r)
    (hleft : 0 ≤ 1 - s * (1 + q + r))
    (omega : ℝ) (homega0 : 0 < omega) (homega1 : omega ≤ 1)
    (rho : ℝ) (hrho : 0 < rho)
    (hpack : G.LocallyPacksInto (B * k))
    (K : ℕ) (hK : 0 < K)
    (hRK : extendedProfileBlockCombinedMeanBound
      rho s omega β q r B k ≤ K)
    (dummyProb : ExtendedProfilePackedBlockState k β q r → ℝ)
    (hdummy0 : ∀ a, 0 ≤ dummyProb a)
    (hdummySum : ∑ a, dummyProb a = 1) :
    ∃ selected : ∀ v (b : Fin B),
        Fin k → G.ExtendedProfileState R0 v,
      (∀ v b,
        0 < G.extendedProfileBlockMass R0 omega v (selected v b)) ∧
      (∀ large : G.ExtendedProfileLargeRow
          (n := B * k) (β := β) (q := q) (r := r),
        G.selectedBlockCapacityLoad R0 rho omega
            (G.encodeExtendedProfileBlockSelection R0 selected)
            (Sum.inl large) /
              extendedProfileCandidateCapacityScale rho s omega β q r <
          ((B * k : ℕ) : ℝ) * rho /
            (extendedProfileCandidateCapacityScale rho s omega β q r *
              extendedProfileSmoothingKappa omega β q r) +
            extendedProfileBlockCombinedDeviation
              rho s omega β q r B k) ∧
      (∀ tiny : G.ExtendedProfileTinyRow (n := B * k),
        G.selectedBlockCapacityLoad R0 rho omega
            (G.encodeExtendedProfileBlockSelection R0 selected)
            (Sum.inr tiny) / ((B * k : ℕ) : ℝ) <
          rho * G.extendedProfileReservoirSize R0 tiny.1
              (selected tiny.1 (extendedProfileColorBlock tiny.2)
                (extendedProfileColorPosition tiny.2)) /
              extendedProfileSmoothingKappa omega β q r +
            extendedProfileCandidateCapacityScale rho s omega β q r /
              ((B * k : ℕ) : ℝ) *
              extendedProfileBlockCombinedDeviation
                rho s omega β q r B k) ∧
      ∀ v,
        G.selectedTotalRawExtendedProfileBlockVariance R0 rho omega
            (G.encodeExtendedProfileBlockSelection R0 selected) v ≤
          extendedProfileBlockSelectedVarianceBound
            rho s omega β q r B k := by
  obtain ⟨selected, hselected, hcapacityRows, hvariance⟩ :=
    G.exists_extendedProfileBlock_capacity_and_variance_meanRelative R0
      hB hk hn hs hspos hq hr0 hleft omega homega0 homega1 rho hrho hpack
      K hK hRK dummyProb hdummy0 hdummySum
  let choice := G.encodeExtendedProfileBlockSelection R0 selected
  let scale := extendedProfileCandidateCapacityScale rho s omega β q r
  let deviation := extendedProfileBlockCombinedDeviation
    rho s omega β q r B k
  have hscale : 0 < scale :=
    extendedProfileCandidateCapacityScale_pos
      (omega := omega) (β := β) (q := q) (r := r)
      hrho hspos homega0
  have hnreal : 0 < (((B * k : ℕ) : ℝ)) := by exact_mod_cast hn
  have hkappa : 0 < extendedProfileSmoothingKappa omega β q r :=
    extendedProfileSmoothingKappa_pos
      (β := β) (q := q) (r := r) homega0 homega1
  refine ⟨selected, hselected, ?_, ?_, ?_⟩
  · intro large
    have hrow := hcapacityRows
      (G.selectedBlockCandidateCapacityRow R0 choice (Sum.inl large))
    rw [G.rowLoad_scaledBlockCandidate_selected_eq_capacityLoad_div
      R0 rho omega scale choice (Sum.inl large)] at hrow
    have hmean := G.rowMean_scaledBlockCandidateCapacityUse_le R0
      hn hs hq hr0 hleft homega0 homega1 hrho hspos
      (G.selectedBlockCandidateCapacityRow R0 choice (Sum.inl large))
    simpa [choice, scale, deviation] using
      hrow.trans_le (add_le_add hmean (le_refl deviation))
  · intro tiny
    let candidate : G.ExtendedProfileTinyCandidateRow R0
        (n := B * k) (β := β) (q := q) (r := r) := {
      center := tiny.1
      color := tiny.2
      candidate := G.decodedExtendedProfileBlockSelection R0 choice
        tiny.1 tiny.2 }
    have hrow := hcapacityRows
      (G.selectedBlockCandidateCapacityRow R0 choice (Sum.inr tiny))
    rw [G.rowLoad_scaledBlockCandidate_selected_eq_capacityLoad_div
      R0 rho omega scale choice (Sum.inr tiny)] at hrow
    have hmean :=
      G.rowMean_scaledBlockTinyCandidateCapacityUse_le_reservoir R0
        hn hs hq hr0 hleft homega0 homega1 hrho hspos candidate
    have hmean' :
        FiniteCategoricalSelection.rowMean
            (fun source a ↦
              G.paddedExtendedProfileBlockProbability R0 omega source.1 a)
            (G.scaledBlockExtendedProfileCandidateCapacityUse
              R0 rho omega scale)
            (G.selectedBlockCandidateCapacityRow R0 choice (Sum.inr tiny)) ≤
          (((B * k : ℕ) : ℝ) * rho *
              G.extendedProfileReservoirSize R0
                candidate.center candidate.candidate) /
            (scale * extendedProfileSmoothingKappa omega β q r) := by
      simpa [candidate, selectedBlockCandidateCapacityRow, scale] using hmean
    have hscaled := hrow.trans_le (add_le_add hmean' (le_refl deviation))
    have hfactor : 0 < scale / (((B * k : ℕ) : ℝ)) :=
      div_pos hscale hnreal
    have hmul := mul_lt_mul_of_pos_left hscaled hfactor
    have hreservoir : candidate.candidate =
        selected tiny.1 (extendedProfileColorBlock tiny.2)
          (extendedProfileColorPosition tiny.2) := by
      simp [candidate, choice]
    have hscaleNe :
        extendedProfileCandidateCapacityScale rho s omega β q r ≠ 0 := by
      simpa only [scale] using hscale.ne'
    dsimp only [scale, deviation] at hmul ⊢
    rw [hreservoir] at hmul
    simp only [candidate] at hmul
    convert hmul using 1 <;>
      field_simp [hscaleNe, hnreal.ne', hkappa.ne'] <;> ring
  · intro v
    have hv :
        G.selectedTotalRawExtendedProfileBlockVariance R0 rho omega
            (G.encodeExtendedProfileBlockSelection R0 selected) v ≤
          extendedProfileBlockVarianceMeanBound rho s omega β q r B k +
            extendedProfileBlockVarianceSelfScale rho s omega β q r B k *
              deviation +
            B * extendedProfileBlockVariancePairScale rho s omega β q r B k *
              deviation := by
      calc
        G.selectedTotalRawExtendedProfileBlockVariance R0 rho omega
            (G.encodeExtendedProfileBlockSelection R0 selected) v ≤
          G.meanTotalExtendedProfileBlockVariance R0 rho omega v +
              extendedProfileBlockVarianceSelfScale rho s omega β q r B k *
                deviation +
            B * extendedProfileBlockVariancePairScale rho s omega β q r B k *
                deviation := hvariance v
        _ ≤ extendedProfileBlockVarianceMeanBound rho s omega β q r B k +
              extendedProfileBlockVarianceSelfScale rho s omega β q r B k *
                deviation +
            B * extendedProfileBlockVariancePairScale rho s omega β q r B k *
                deviation := by
          gcongr
          exact G.meanTotalExtendedProfileBlockVariance_le R0
            hB hk hn hs hspos hq hr0 hleft homega0 homega1
            rho hrho.le hpack v
    simpa [extendedProfileBlockSelectedVarianceBound, deviation] using hv

end WeightedSimpleGraph

end

end WeightedEdgeColoring
