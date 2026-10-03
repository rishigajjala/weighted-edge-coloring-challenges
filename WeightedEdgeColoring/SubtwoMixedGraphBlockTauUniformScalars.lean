import WeightedEdgeColoring.SubtwoMixedGraphBlockUniformScalars
import WeightedEdgeColoring.SubtwoMixedGraphJointScalarBudget

/-! One graph-independent threshold for the block selector's dyadic margins,
label discrepancy, and sharp variance error. -/

namespace WeightedEdgeColoring

noncomputable section

namespace WeightedMultigraph

theorem blockCount_le_of_colorBudget
    {B k n C1 : ℕ} (hk : 0 < k) (hcolors : B * k ≤ C1 * n) :
    (B : ℝ) ≤ ((C1 : ℝ) / k) * n := by
  have hkR : (0 : ℝ) < k := by exact_mod_cast hk
  have hreal : (B : ℝ) * k ≤ (C1 : ℝ) * n := by
    exact_mod_cast hcolors
  calc
    (B : ℝ) = ((B : ℝ) * k) / k := by field_simp
    _ ≤ ((C1 : ℝ) * n) / k :=
      div_le_div_of_nonneg_right hreal hkR.le
    _ = ((C1 : ℝ) / k) * n := by ring

theorem mixedBlock_jointProfile_errors_eventually
    {Label : Type*} [Fintype Label] [DecidableEq Label]
    {k L : ℕ} {tau C0 D t eta : ℝ}
    (htau0 : 0 < tau) (htau1 : tau ≤ 1 / 4)
    (hL : 0 < L) (hC0 : 0 < C0) (hD : 0 ≤ D)
    (ht : 0 < t) (heta : 0 < eta) :
    ∃ N : ℕ, ∀ n B : ℕ, N ≤ n → (B : ℝ) ≤ D * n →
      let s := jointProfileS tau
      let beta := jointProfileBeta tau
      let qstep := jointProfileQ tau
      let r := jointProfileR tau
      let rho := jointProfileRho tau
      let omega := jointProfileOmega tau
      let A := mixedCandidateOrientedScale (Label := Label)
        (β := beta) (qstep := qstep) (r := r) rho s omega C0
      let U := mixedBlockVarianceUnitScale (k := k) (s := s)
        (Label := Label) (β := beta) (qstep := qstep) (r := r)
        n rho omega C0
      let scale := (L : ℝ) * A
      let meanBound := 1 + (n : ℝ) * (rho / (1 - omega)) /
        scale + n + 2 * B
      let columnBound :=
        (k : ℝ) * mixedCandidateWeightedPerColorColumnBound
          (Label := Label) (β := beta) (qstep := qstep) (r := r) n +
        ((mixedGraphAtomBound (Label := Label)
          (β := beta) (qstep := qstep) (r := r) : ℝ) ^ k) * n + 1 +
        Fintype.card (Option Label)
      let deviation := FinitePartialResamplingNumerics.packingDeviation
        meanBound columnBound
      scale / (n : ℝ) * deviation ≤ tau ^ 2 / 4 ∧
      rho / (1 - omega) + scale / (n : ℝ) * deviation ≤
        1 - tau / 2 ∧
      scale / (n : ℝ) * deviation + 2 * beta ≤
        (1 - rho / (1 - omega)) * r ∧
      (k : ℝ) * deviation ≤ eta * n ∧
      t * n + (B : ℝ) *
        (A * (rho * s) + ((n : ℝ) + B * L) * U * deviation) /
          (4 * t) ≤
        (t + D * (A * (rho * s)) / (4 * t) + eta) * n := by
  rcases jointProfile_parameters htau0 htau1 with
    ⟨hs, hbeta, _, _, homega, _, _, _, hrho, _, _⟩
  have homega1 : jointProfileOmega tau < 1 := by
    unfold jointProfileOmega
    linarith
  let A := mixedCandidateOrientedScale (Label := Label)
    (β := jointProfileBeta tau) (qstep := jointProfileQ tau)
    (r := jointProfileR tau)
    (jointProfileRho tau) (jointProfileS tau)
    (jointProfileOmega tau) C0
  let scale : ℝ := L * A
  have hA : 0 < A := mixedCandidateOrientedScale_pos
    hrho hs homega hC0
  have hscale : 0 < scale := mul_pos (by exact_mod_cast hL) hA
  let epsScale := tau ^ 2 / (4 * scale)
  have hepsScale : 0 < epsScale := by dsimp [epsScale]; positivity
  let epsLabel := eta / ((k : ℝ) + 1)
  have hepsLabel : 0 < epsLabel := by dsimp [epsLabel]; positivity
  obtain ⟨N1, hdev1⟩ := mixedBlockJoint_deviation_sublinear
    (Label := Label) (k := k) (L := L)
    (β := jointProfileBeta tau) (qstep := jointProfileQ tau)
    (r := jointProfileR tau) (rho := jointProfileRho tau)
    (s := jointProfileS tau) (omega := jointProfileOmega tau)
    (C0 := C0) (B0 := D) (ε := epsScale)
    hbeta (by exact_mod_cast hL) hrho hs homega homega1 hC0 hD
    hepsScale
  obtain ⟨N2, hdev2⟩ := mixedBlockJoint_deviation_sublinear
    (Label := Label) (k := k) (L := L)
    (β := jointProfileBeta tau) (qstep := jointProfileQ tau)
    (r := jointProfileR tau) (rho := jointProfileRho tau)
    (s := jointProfileS tau) (omega := jointProfileOmega tau)
    (C0 := C0) (B0 := D) (ε := epsLabel)
    hbeta (by exact_mod_cast hL) hrho hs homega homega1 hC0 hD
    hepsLabel
  obtain ⟨N3, hres⟩ := mixedBlockJoint_residualBudget_eventually
    (Label := Label) (k := k) (L := L)
    (β := jointProfileBeta tau) (qstep := jointProfileQ tau)
    (r := jointProfileR tau) (rho := jointProfileRho tau)
    (s := jointProfileS tau) (omega := jointProfileOmega tau)
    (C0 := C0) (D := D) (t := t) (η := eta)
    hbeta (by exact_mod_cast hL) hrho hs homega homega1 hC0 hD
    ht heta
  refine ⟨max 1 (max N1 (max N2 N3)), ?_⟩
  intro n B hn hB
  dsimp only
  have hnR : (0 : ℝ) < n := by
    have h : 1 ≤ n := (le_max_left 1 _).trans hn
    exact_mod_cast h
  have hn1 : N1 ≤ n :=
    (le_max_left N1 _).trans ((le_max_right 1 _).trans hn)
  have hn2 : N2 ≤ n :=
    (le_max_left N2 N3).trans
      ((le_max_right N1 _).trans ((le_max_right 1 _).trans hn))
  have hn3 : N3 ≤ n :=
    (le_max_right N2 N3).trans
      ((le_max_right N1 _).trans ((le_max_right 1 _).trans hn))
  let scale0 := (L : ℝ) * A
  let meanBound := 1 + (n : ℝ) *
    (jointProfileRho tau / (1 - jointProfileOmega tau)) /
    scale0 + n + 2 * B
  let columnBound :=
    (k : ℝ) * mixedCandidateWeightedPerColorColumnBound
      (Label := Label) (β := jointProfileBeta tau)
      (qstep := jointProfileQ tau) (r := jointProfileR tau) n +
    ((mixedGraphAtomBound (Label := Label)
      (β := jointProfileBeta tau) (qstep := jointProfileQ tau)
      (r := jointProfileR tau) : ℝ) ^ k) * n + 1 +
    Fintype.card (Option Label)
  let deviation := FinitePartialResamplingNumerics.packingDeviation
    meanBound columnBound
  have hd1 : deviation ≤ epsScale * n := hdev1 n B hn1 hB
  have hd2 : deviation ≤ epsLabel * n := hdev2 n B hn2 hB
  have hscaleEq : scale0 = scale := rfl
  have hscaleEps : scale0 * epsScale = tau ^ 2 / 4 := by
    dsimp [scale0, epsScale, scale]
    field_simp
  have hscaled : scale0 / (n : ℝ) * deviation ≤ tau ^ 2 / 4 := by
    have h : scale0 * deviation ≤ scale0 * (epsScale * n) :=
      mul_le_mul_of_nonneg_left hd1 (by rw [hscaleEq]; exact hscale.le)
    calc
      scale0 / (n : ℝ) * deviation =
          (scale0 * deviation) / n := by ring
      _ ≤ (scale0 * (epsScale * n)) / n :=
        div_le_div_of_nonneg_right h hnR.le
      _ = tau ^ 2 / 4 := by
        rw [← mul_assoc, hscaleEps]
        field_simp [hnR.ne']
  have hk_eps : (k : ℝ) * epsLabel ≤ eta := by
    dsimp [epsLabel]
    have hden : 0 < (k : ℝ) + 1 := by positivity
    have hratio : (k : ℝ) / ((k : ℝ) + 1) ≤ 1 :=
      (div_le_one hden).2 (by linarith)
    calc
      (k : ℝ) * (eta / ((k : ℝ) + 1)) =
          ((k : ℝ) / ((k : ℝ) + 1)) * eta := by ring
      _ ≤ 1 * eta := mul_le_mul_of_nonneg_right hratio heta.le
      _ = eta := one_mul _
  have hlabel : (k : ℝ) * deviation ≤ eta * n := by
    have h1 := mul_le_mul_of_nonneg_left hd2 (Nat.cast_nonneg k)
    have h2 := mul_le_mul_of_nonneg_right hk_eps hnR.le
    nlinarith
  have hresidual := hres n B hn3 hB
  dsimp only at hresidual
  refine ⟨hscaled, ?_, ?_, hlabel, ?_⟩
  · exact jointProfile_selectedCandidate_bound_le_slotTarget
      htau0 htau1 hscaled
  · exact jointProfile_selectedTiny_margin htau0 htau1 hscaled
  · exact hresidual

end WeightedMultigraph

end
end WeightedEdgeColoring
