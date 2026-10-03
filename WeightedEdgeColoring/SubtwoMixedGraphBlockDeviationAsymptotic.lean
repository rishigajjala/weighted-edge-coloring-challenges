import WeightedEdgeColoring.SubtwoMixedGraphBlockLabelSelected
import WeightedEdgeColoring.PackingDeviationPolynomialColumn

/-! Graph-order-independent sublinearity of the mixed block deviation. -/

namespace WeightedEdgeColoring

noncomputable section

namespace WeightedMultigraph

theorem mixedBlockJoint_deviation_sublinear
    {Label : Type*} [Fintype Label] [DecidableEq Label]
    {k L : ℕ} {β qstep r rho s omega C0 B0 ε : ℝ}
    (hβ : 0 < β) (hL : 0 < L) (hrho : 0 < rho) (hs : 0 < s)
    (homega0 : 0 < omega) (homega1 : omega < 1)
    (hC0 : 0 < C0) (hB0 : 0 ≤ B0) (hε : 0 < ε) :
    ∃ N : ℕ, ∀ n B : ℕ, N ≤ n → (B : ℝ) ≤ B0 * n →
      let candidateScale := (L : ℝ) *
        mixedCandidateOrientedScale (Label := Label)
          (β := β) (qstep := qstep) (r := r) rho s omega C0
      let meanBound := 1 + (n : ℝ) * (rho / (1 - omega)) /
        candidateScale + n + 2 * B
      let columnBound :=
        (k : ℝ) * mixedCandidateWeightedPerColorColumnBound
          (Label := Label) (β := β) (qstep := qstep) (r := r) n +
        ((mixedGraphAtomBound (Label := Label)
          (β := β) (qstep := qstep) (r := r) : ℝ) ^ k) * n + 1 +
        Fintype.card (Option Label)
      FinitePartialResamplingNumerics.packingDeviation
        meanBound columnBound ≤ ε * n := by
  let candidateScale := (L : ℝ) *
    mixedCandidateOrientedScale (Label := Label)
      (β := β) (qstep := qstep) (r := r) rho s omega C0
  let atom : ℝ := mixedGraphAtomBound (Label := Label)
    (β := β) (qstep := qstep) (r := r)
  let slots : ℝ := explicitLargeSlotBound β qstep r
  let factor : ℝ := atom * (slots / β + 1)
  let A : ℝ := 2 + (rho / (1 - omega)) / candidateScale + 2 * B0
  let C : ℝ := (k : ℝ) * factor + atom ^ k + 1 +
    Fintype.card (Option Label)
  have hcandidate : 0 < candidateScale := by
    dsimp [candidateScale]
    exact mul_pos (by exact_mod_cast hL)
      (mixedCandidateOrientedScale_pos (Label := Label)
        (β := β) (qstep := qstep) (r := r)
        hrho hs homega0 hC0)
  have hfactor : 0 ≤ factor := by
    dsimp [factor, atom, slots]
    positivity
  have hA : 0 ≤ A := by
    dsimp [A]
    have hrate : 0 ≤ rho / (1 - omega) :=
      (div_pos hrho (sub_pos.mpr homega1)).le
    positivity
  have hC : 0 ≤ C := by
    dsimp [C, atom, factor]
    positivity
  obtain ⟨N0, hdev⟩ :=
    FinitePartialResamplingNumerics.packingDeviation_sublinear_of_linear_row_polynomial_column
      hA hC 1 ε hε
  refine ⟨max 1 N0, ?_⟩
  intro n B hn hB
  dsimp only
  have hn1 : 1 ≤ n := (le_max_left 1 N0).trans hn
  have hN0 : N0 ≤ n := (le_max_right 1 N0).trans hn
  have hnR : (1 : ℝ) ≤ n := by exact_mod_cast hn1
  have hn0 : (0 : ℝ) ≤ n := Nat.cast_nonneg _
  let meanBound := 1 + (n : ℝ) * (rho / (1 - omega)) /
    candidateScale + n + 2 * B
  let columnBound :=
    (k : ℝ) * mixedCandidateWeightedPerColorColumnBound
      (Label := Label) (β := β) (qstep := qstep) (r := r) n +
    ((mixedGraphAtomBound (Label := Label)
      (β := β) (qstep := qstep) (r := r) : ℝ) ^ k) * n + 1 +
    Fintype.card (Option Label)
  have hrow0 : 0 ≤ meanBound := by
    dsimp [meanBound]
    have hrate : 0 ≤ rho / (1 - omega) :=
      (div_pos hrho (sub_pos.mpr homega1)).le
    positivity
  have hcol0 : 0 ≤ columnBound := by
    dsimp [columnBound, mixedCandidateWeightedPerColorColumnBound]
    positivity
  have hrow : meanBound ≤ A * n := by
    dsimp [meanBound, A]
    have hrate : 0 ≤ rho / (1 - omega) :=
      (div_pos hrho (sub_pos.mpr homega1)).le
    have hformula : (n : ℝ) * (rho / (1 - omega)) /
        candidateScale =
      ((rho / (1 - omega)) / candidateScale) * n := by ring
    rw [hformula]
    nlinarith
  have hcol : columnBound ≤ C * (n : ℝ) ^ 1 := by
    dsimp [columnBound, C, factor,
      mixedCandidateWeightedPerColorColumnBound]
    have hconstant : (1 + Fintype.card (Option Label) : ℝ) ≤
        (1 + Fintype.card (Option Label) : ℝ) * n := by
      exact le_mul_of_one_le_right (by positivity) hnR
    nlinarith
  exact hdev n hN0 meanBound columnBound hrow0 hcol0 hrow hcol

end WeightedMultigraph

end
end WeightedEdgeColoring
