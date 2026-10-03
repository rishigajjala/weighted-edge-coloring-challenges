import WeightedEdgeColoring.ExtendedProfileBlockVarianceSelection
import WeightedEdgeColoring.ExtendedProfileBlockCandidateCapacityRows
import WeightedEdgeColoring.ExtendedProfileBlockVarianceBounds
import WeightedEdgeColoring.ExtendedProfileBlockQuadraticBridge

/-!
# One block selection for capacity and quadratic rows

This is the concrete deterministic endpoint of the block construction.  A
single supported categorical choice controls all candidate capacity rows and
both levels of the block-variance rows.  The remaining inputs `K` and the
dummy state law are only the finite offset encoding required by the generic
mean-relative selector.
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

def extendedProfileBlockCombinedMeanBound
    (rho s omega β q r : ℝ) (B k : ℕ) : ℝ :=
  (B * k : ℕ) +
    ((B * k : ℕ) : ℝ) * rho /
      (extendedProfileCandidateCapacityScale rho s omega β q r *
        extendedProfileSmoothingKappa omega β q r)

def extendedProfileBlockCombinedColumnBound
    (B k : ℕ) (β q r : ℝ) : ℝ :=
  k * extendedProfileCandidateCapacityColumnBound (B * k) β q r +
    extendedProfileBlockVarianceColumnBound B k β q r

/-- The one-call packing deviation used by the simultaneous capacity and
quadratic selector. -/
def extendedProfileBlockCombinedDeviation
    (rho s omega β q r : ℝ) (B k : ℕ) : ℝ :=
  FinitePartialResamplingNumerics.packingDeviation
    (extendedProfileBlockCombinedMeanBound rho s omega β q r B k)
    (extendedProfileBlockCombinedColumnBound B k β q r)

/-- The resulting explicit bound for the selected sum of raw block
variances at one vertex. -/
def extendedProfileBlockSelectedVarianceBound
    (rho s omega β q r : ℝ) (B k : ℕ) : ℝ :=
  extendedProfileBlockVarianceMeanBound rho s omega β q r B k +
    extendedProfileBlockVarianceSelfScale rho s omega β q r B k *
      extendedProfileBlockCombinedDeviation rho s omega β q r B k +
    B * extendedProfileBlockVariancePairScale rho s omega β q r B k *
      extendedProfileBlockCombinedDeviation rho s omega β q r B k

/-- Fully simplified whole-edge quadratic budget.  Its leading term is
linear in the number `B` of blocks, while its error coefficient is independent
of `B`. -/
def extendedProfileBlockQuadraticBound
    (rho s omega β q r : ℝ) (B k : ℕ) : ℝ :=
  B * (((explicitLargeSlotBound β q r : ℝ) + 1) *
      extendedProfileCandidateCapacityScale rho s omega β q r *
        (rho * s)) +
    (k + 1) *
      (extendedProfileBlockVarianceAmplitude rho s omega β q r) ^ 2 *
        extendedProfileBlockCombinedDeviation rho s omega β q r B k

theorem B_mul_extendedProfileBlockSelectedVarianceBound_eq
    (hB : 0 < B) (hk : 0 < k) :
    B * extendedProfileBlockSelectedVarianceBound
        rho s omega β q r B k =
      extendedProfileBlockQuadraticBound rho s omega β q r B k := by
  let D := extendedProfileBlockCombinedDeviation rho s omega β q r B k
  let A := extendedProfileBlockVarianceAmplitude rho s omega β q r
  have hmean := extendedProfileBlockVarianceMeanBound_eq
    (rho := rho) (s := s) (omega := omega) (β := β) (q := q) (r := r)
    (B := B) (k := k) hB hk
  have hself := B_mul_extendedProfileBlockVarianceSelfScale_eq
    (rho := rho) (s := s) (omega := omega) (β := β) (q := q) (r := r)
    (B := B) (k := k) hB hk
  have hpair := B_sq_mul_extendedProfileBlockVariancePairScale_eq
    (rho := rho) (s := s) (omega := omega) (β := β) (q := q) (r := r)
    (B := B) (k := k) hB hk
  unfold extendedProfileBlockSelectedVarianceBound
    extendedProfileBlockQuadraticBound
  rw [hmean]
  calc
    (B : ℝ) *
        (((explicitLargeSlotBound β q r : ℝ) + 1) *
            extendedProfileCandidateCapacityScale rho s omega β q r *
              (rho * s) +
          extendedProfileBlockVarianceSelfScale
              rho s omega β q r B k * D +
          B * extendedProfileBlockVariancePairScale
              rho s omega β q r B k * D) =
      B * (((explicitLargeSlotBound β q r : ℝ) + 1) *
          extendedProfileCandidateCapacityScale rho s omega β q r *
            (rho * s)) +
        (B * extendedProfileBlockVarianceSelfScale
            rho s omega β q r B k) * D +
        (B * B * extendedProfileBlockVariancePairScale
            rho s omega β q r B k) * D := by ring
    _ = B * (((explicitLargeSlotBound β q r : ℝ) + 1) *
          extendedProfileCandidateCapacityScale rho s omega β q r *
            (rho * s)) +
        (k + 1) * A ^ 2 * D := by rw [hself, hpair]; ring

/-- Simultaneous block capacity and quadratic selection. -/
theorem exists_extendedProfileBlock_capacity_and_variance
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
      (∀ row : G.ExtendedProfileCapacityRow
          (n := B * k) (β := β) (q := q) (r := r),
        G.selectedBlockCapacityLoad R0 rho omega
            (G.encodeExtendedProfileBlockSelection R0 selected) row /
              extendedProfileCandidateCapacityScale rho s omega β q r <
          ((B * k : ℕ) : ℝ) * rho /
            (extendedProfileCandidateCapacityScale rho s omega β q r *
              extendedProfileSmoothingKappa omega β q r) +
            FinitePartialResamplingNumerics.packingDeviation
              (extendedProfileBlockCombinedMeanBound
                rho s omega β q r B k)
              (extendedProfileBlockCombinedColumnBound B k β q r)) ∧
      ∀ v,
        G.selectedTotalRawExtendedProfileBlockVariance R0 rho omega
            (G.encodeExtendedProfileBlockSelection R0 selected) v ≤
          extendedProfileBlockVarianceMeanBound
              rho s omega β q r B k +
            extendedProfileBlockVarianceSelfScale
                rho s omega β q r B k *
              FinitePartialResamplingNumerics.packingDeviation
                (extendedProfileBlockCombinedMeanBound
                  rho s omega β q r B k)
                (extendedProfileBlockCombinedColumnBound B k β q r) +
            B * extendedProfileBlockVariancePairScale
                rho s omega β q r B k *
              FinitePartialResamplingNumerics.packingDeviation
                (extendedProfileBlockCombinedMeanBound
                  rho s omega β q r B k)
                (extendedProfileBlockCombinedColumnBound B k β q r) := by
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
  · intro row
    let choice := G.encodeExtendedProfileBlockSelection R0 selected
    have hrow := hcapacityRows
      (G.selectedBlockCandidateCapacityRow R0 choice row)
    rw [G.rowLoad_scaledBlockCandidate_selected_eq_capacityLoad_div
      R0 rho omega capScale choice row] at hrow
    have hmean := G.rowMean_scaledBlockCandidateCapacityUse_le R0
      hn hs hq hr0 hleft homega0 homega1 hrho hspos
      (G.selectedBlockCandidateCapacityRow R0 choice row)
    exact hrow.trans_le (add_le_add hmean (le_refl _))
  · intro v
    calc
      G.selectedTotalRawExtendedProfileBlockVariance R0 rho omega
          (G.encodeExtendedProfileBlockSelection R0 selected) v ≤
        G.meanTotalExtendedProfileBlockVariance R0 rho omega v +
            selfScale * FinitePartialResamplingNumerics.packingDeviation R C +
          B * pairScale *
            FinitePartialResamplingNumerics.packingDeviation R C :=
        hvariance v
      _ ≤ extendedProfileBlockVarianceMeanBound rho s omega β q r B k +
            selfScale * FinitePartialResamplingNumerics.packingDeviation R C +
          B * pairScale *
            FinitePartialResamplingNumerics.packingDeviation R C := by
        gcongr
        exact G.meanTotalExtendedProfileBlockVariance_le R0
          hB hk hn hs hspos hq hr0 hleft homega0 homega1
          rho hrho.le hpack v

/-- The explicit selected-variance bound gives both the whole-edge
quadratic estimate and the squared signed first-moment deficit.  This is the
analytic bridge used after the simultaneous selector; it needs no further
probabilistic choice. -/
theorem selectedBlock_quadratic_and_signedDeficit_le
    (hB : 0 < B) (rho omega : ℝ)
    (choice : (G.V × Fin B) → ExtendedProfilePackedBlockState k β q r)
    (hvariance : ∀ v,
      G.selectedTotalRawExtendedProfileBlockVariance R0 rho omega choice v ≤
        extendedProfileBlockSelectedVarianceBound
          rho s omega β q r B k) :
    (∀ v,
      (∑ e : G.StarEdge v,
        G.weight e.1 *
          (G.selectedExtendedProfileTotalOptionMass
              R0 rho omega choice e.1 - rho * s) ^ 2) ≤
        B * extendedProfileBlockSelectedVarianceBound
          rho s omega β q r B k) ∧
    ∀ v,
      (∑ e : G.StarEdge v, G.weight e.1 *
        (rho * s -
          G.selectedExtendedProfileTotalOptionMass
            R0 rho omega choice e.1)) ^ 2 ≤
        G.starWeight v *
          (B * extendedProfileBlockSelectedVarianceBound
            rho s omega β q r B k) := by
  constructor
  · intro v
    exact (G.selectedStarTotalOptionMass_quadratic_le
      R0 hB rho omega choice v).trans
        (mul_le_mul_of_nonneg_left (hvariance v) (Nat.cast_nonneg B))
  · intro v
    have hstar : 0 ≤ G.starWeight v := by
      unfold starWeight
      exact Finset.sum_nonneg fun e _he ↦ G.weight_nonneg e.1
    exact (G.selectedStarTotalOptionMass_signedDeficit_sq_le
      R0 hB rho omega choice v).trans
        (mul_le_mul_of_nonneg_left
          (mul_le_mul_of_nonneg_left (hvariance v) (Nat.cast_nonneg B))
          hstar)

/-- The preceding bridge with the scale algebra fully simplified. -/
theorem selectedBlock_quadratic_and_signedDeficit_le_explicit
    (hB : 0 < B) (hk : 0 < k) (rho omega : ℝ)
    (choice : (G.V × Fin B) → ExtendedProfilePackedBlockState k β q r)
    (hvariance : ∀ v,
      G.selectedTotalRawExtendedProfileBlockVariance R0 rho omega choice v ≤
        extendedProfileBlockSelectedVarianceBound
          rho s omega β q r B k) :
    (∀ v,
      (∑ e : G.StarEdge v,
        G.weight e.1 *
          (G.selectedExtendedProfileTotalOptionMass
              R0 rho omega choice e.1 - rho * s) ^ 2) ≤
        extendedProfileBlockQuadraticBound
          rho s omega β q r B k) ∧
    ∀ v,
      (∑ e : G.StarEdge v, G.weight e.1 *
        (rho * s -
          G.selectedExtendedProfileTotalOptionMass
            R0 rho omega choice e.1)) ^ 2 ≤
        G.starWeight v *
          extendedProfileBlockQuadraticBound
            rho s omega β q r B k := by
  have h := G.selectedBlock_quadratic_and_signedDeficit_le
    R0 hB rho omega choice hvariance
  rw [B_mul_extendedProfileBlockSelectedVarianceBound_eq
    (rho := rho) (s := s) (omega := omega) (β := β) (q := q) (r := r)
    (B := B) (k := k) hB hk] at h
  exact h

end WeightedSimpleGraph

end

end WeightedEdgeColoring
