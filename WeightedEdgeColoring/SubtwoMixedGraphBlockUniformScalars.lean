import WeightedEdgeColoring.SubtwoMixedGraphBlockResidualScalars

/-! Uniform graph-order-free residual error for fixed mixed block length. -/

namespace WeightedEdgeColoring

noncomputable section

namespace WeightedMultigraph

theorem mixedBlockJoint_residualBudget_eventually
    {Label : Type*} [Fintype Label] [DecidableEq Label]
    {k L : ℕ} {β qstep r rho s omega C0 D t η : ℝ}
    (hβ : 0 < β) (hL : 0 < L) (hrho : 0 < rho) (hs : 0 < s)
    (homega0 : 0 < omega) (homega1 : omega < 1)
    (hC0 : 0 < C0) (hD : 0 ≤ D) (ht : 0 < t) (hη : 0 < η) :
    ∃ N : ℕ, ∀ n B : ℕ, N ≤ n → (B : ℝ) ≤ D * n →
      let A := mixedCandidateOrientedScale (Label := Label)
        (β := β) (qstep := qstep) (r := r) rho s omega C0
      let U := mixedBlockVarianceUnitScale (k := k) (s := s)
        (Label := Label) (β := β) (qstep := qstep) (r := r)
        n rho omega C0
      let candidateScale := (L : ℝ) * A
      let meanBound := 1 + (n : ℝ) * (rho / (1 - omega)) /
        candidateScale + n + 2 * B
      let columnBound :=
        (k : ℝ) * mixedCandidateWeightedPerColorColumnBound
          (Label := Label) (β := β) (qstep := qstep) (r := r) n +
        ((mixedGraphAtomBound (Label := Label)
          (β := β) (qstep := qstep) (r := r) : ℝ) ^ k) * n + 1 +
        Fintype.card (Option Label)
      let δ := FinitePartialResamplingNumerics.packingDeviation
        meanBound columnBound
      t * n + (B : ℝ) *
        (A * (rho * s) + ((n : ℝ) + B * L) * U * δ) / (4 * t) ≤
        (t + D * (A * (rho * s)) / (4 * t) + η) * n := by
  let A := mixedCandidateOrientedScale (Label := Label)
    (β := β) (qstep := qstep) (r := r) rho s omega C0
  let H : ℝ := D * (1 + D * L) *
    ((k : ℝ) * (A + rho * s * C0)) ^ 2 / (4 * t)
  have hH : 0 ≤ H := by dsimp [H]; positivity
  let ε : ℝ := η / (H + 1)
  have hε : 0 < ε := div_pos hη (by linarith)
  obtain ⟨N0, hdev⟩ := mixedBlockJoint_deviation_sublinear
    (Label := Label) (k := k) (L := L)
    (β := β) (qstep := qstep) (r := r)
    (rho := rho) (s := s) (omega := omega)
    (C0 := C0) (B0 := D) (ε := ε)
    hβ hL hrho hs homega0 homega1 hC0 hD hε
  refine ⟨max 1 N0, ?_⟩
  intro n B hn hB
  dsimp only
  have hn1 : 1 ≤ n := (le_max_left 1 N0).trans hn
  have hN0 : N0 ≤ n := (le_max_right 1 N0).trans hn
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn1
  let U := mixedBlockVarianceUnitScale (k := k) (s := s)
    (Label := Label) (β := β) (qstep := qstep) (r := r)
    n rho omega C0
  let candidateScale := (L : ℝ) * A
  let meanBound := 1 + (n : ℝ) * (rho / (1 - omega)) /
    candidateScale + n + 2 * B
  let columnBound :=
    (k : ℝ) * mixedCandidateWeightedPerColorColumnBound
      (Label := Label) (β := β) (qstep := qstep) (r := r) n +
    ((mixedGraphAtomBound (Label := Label)
      (β := β) (qstep := qstep) (r := r) : ℝ) ^ k) * n + 1 +
    Fintype.card (Option Label)
  let δ := FinitePartialResamplingNumerics.packingDeviation
    meanBound columnBound
  have hδ : δ ≤ ε * n := hdev n B hN0 hB
  have hmean0 : 0 ≤ meanBound := by
    dsimp [meanBound, candidateScale, A]
    have hA : 0 < mixedCandidateOrientedScale (Label := Label)
        (β := β) (qstep := qstep) (r := r) rho s omega C0 :=
      mixedCandidateOrientedScale_pos hrho hs homega0 hC0
    have hrate : 0 ≤ rho / (1 - omega) :=
      (div_pos hrho (sub_pos.mpr homega1)).le
    positivity
  have hcolumn0 : 0 ≤ columnBound := by
    dsimp [columnBound, mixedCandidateWeightedPerColorColumnBound]
    positivity
  have hδ0 : 0 ≤ δ := by
    dsimp [δ, FinitePartialResamplingNumerics.packingDeviation]
    have hlog := FinitePartialResamplingNumerics.packingLog_nonneg hcolumn0
    positivity
  have hS : 0 ≤ A * (rho * s) := by
    dsimp [A]
    have hA := mixedCandidateOrientedScale_nonneg
      (Label := Label) (β := β) (qstep := qstep) (r := r)
      hrho.le hs.le homega0 hC0.le
    positivity
  have hraw := mixedBlockStarResidualBudget_le
    hnR ht (Nat.cast_nonneg B) (Nat.cast_nonneg L)
    hD hS hδ0 hε.le hB hδ
    (k := (k : ℝ)) (A := A + rho * s * C0)
  have hU : U = ((k : ℝ) * (A + rho * s * C0) / n) ^ 2 := rfl
  rw [← hU] at hraw
  have hHε : H * ε ≤ η := by
    dsimp [ε]
    have hdiv : H / (H + 1) ≤ 1 :=
      (div_le_one (by linarith)).2 (by linarith)
    calc
      H * (η / (H + 1)) = (H / (H + 1)) * η := by ring
      _ ≤ 1 * η := mul_le_mul_of_nonneg_right hdiv hη.le
      _ = η := one_mul _
  have hfinal := mul_le_mul_of_nonneg_right hHε hnR.le
  change (D * (1 + D * L) *
    ((k : ℝ) * (A + rho * s * C0)) ^ 2 / (4 * t)) * ε * n ≤
      η * n at hfinal
  have hcoeff :
      D * (1 + D * L) *
          ((k : ℝ) * (A + rho * s * C0)) ^ 2 * ε / (4 * t) =
        (D * (1 + D * L) *
          ((k : ℝ) * (A + rho * s * C0)) ^ 2 / (4 * t)) * ε := by
    ring
  rw [hcoeff] at hraw
  change t * n + (B : ℝ) *
      (A * (rho * s) + ((n : ℝ) + B * L) * U * δ) / (4 * t) ≤
    (t + D * (A * (rho * s)) / (4 * t) + η) * n
  nlinarith [hraw, hfinal]

end WeightedMultigraph

end
end WeightedEdgeColoring
