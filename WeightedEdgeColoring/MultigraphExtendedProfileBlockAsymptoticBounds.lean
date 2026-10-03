import WeightedEdgeColoring.MultigraphExtendedProfileBlockCapacityVarianceSelection
import WeightedEdgeColoring.PackingDeviationPolynomialColumn

/-!
# Asymptotic size of the block-selector deviation

For fixed profile parameters and fixed block width `k`, the simultaneous
selector has a row bound linear in the exact palette size `B*k` and a column
bound quadratic in it.  The polynomial-column numerical lemma therefore
makes its packing deviation `o(B*k)`.
-/

namespace WeightedEdgeColoring

noncomputable section

namespace WeightedMultigraph

/-- Coefficient of the linear row envelope. -/
def extendedProfileBlockCombinedMeanCoefficient
    (L : ℕ) (rho s omega β q r : ℝ) : ℝ :=
  1 + rho /
    (((L : ℝ) * extendedProfileCandidateCapacityScale rho s omega β q r) *
      extendedProfileSmoothingKappa omega β q r)

/-- Coefficient of a quadratic envelope for the combined source--state
column bound. -/
def extendedProfileBlockCombinedColumnCoefficient
    (k : ℕ) (β q r : ℝ) : ℝ :=
  k * extendedProfileStateBound β q r *
      (explicitLargeSlotBound β q r / β + 1) +
    (extendedProfileStateBound β q r : ℝ) ^ k + 1

theorem extendedProfileBlockCombinedMeanBound_eq_linear
    (L : ℕ) (rho s omega β q r : ℝ) (B k : ℕ) :
    extendedProfileBlockCombinedMeanBound L rho s omega β q r B k =
      extendedProfileBlockCombinedMeanCoefficient L rho s omega β q r *
        (B * k) := by
  unfold extendedProfileBlockCombinedMeanBound
    extendedProfileBlockCombinedMeanCoefficient
  push_cast
  ring

theorem extendedProfileBlockCombinedMeanCoefficient_nonneg
    {L : ℕ} {rho s omega β q r : ℝ}
    (hrho : 0 ≤ rho) (hs : 0 ≤ s)
    (homega0 : 0 < omega) (homega1 : omega ≤ 1) :
    0 ≤ extendedProfileBlockCombinedMeanCoefficient
      L rho s omega β q r := by
  unfold extendedProfileBlockCombinedMeanCoefficient
  have hscale : 0 ≤
      extendedProfileCandidateCapacityScale rho s omega β q r :=
    extendedProfileCandidateCapacityScale_nonneg hrho hs
  have hkappa : 0 ≤ extendedProfileSmoothingKappa omega β q r :=
    (extendedProfileSmoothingKappa_pos
      (β := β) (q := q) (r := r) homega0 homega1).le
  positivity

theorem extendedProfileBlockCombinedColumnCoefficient_nonneg
    {k : ℕ} {β q r : ℝ} (hβ : 0 < β) :
    0 ≤ extendedProfileBlockCombinedColumnCoefficient k β q r := by
  unfold extendedProfileBlockCombinedColumnCoefficient
  positivity

/-- The concrete combined column bound is at most a fixed coefficient times
the square of the palette size. -/
theorem extendedProfileBlockCombinedColumnBound_le_quadratic
    {B k : ℕ} {β q r : ℝ} (hβ : 0 < β) (hn : 1 ≤ B * k) :
    extendedProfileBlockCombinedColumnBound B k β q r ≤
      extendedProfileBlockCombinedColumnCoefficient k β q r *
        ((B * k : ℕ) : ℝ) ^ 2 := by
  have hnR : (1 : ℝ) ≤ (B : ℝ) * k := by
    exact_mod_cast hn
  have hn_sq : (B : ℝ) * k ≤ ((B : ℝ) * k) ^ 2 := by
    nlinarith
  have hone_sq : (1 : ℝ) ≤ ((B : ℝ) * k) ^ 2 := by
    nlinarith
  have hMpow : 0 ≤ (extendedProfileStateBound β q r : ℝ) ^ k := by
    positivity
  unfold extendedProfileBlockCombinedColumnBound
    extendedProfileCandidateCapacityColumnBound
    extendedProfileBlockVarianceColumnBound
    extendedProfileBlockCombinedColumnCoefficient
  push_cast
  calc
    (k : ℝ) * (((B : ℝ) * k) ^ 2 *
          (extendedProfileStateBound β q r : ℝ) *
            ((explicitLargeSlotBound β q r : ℝ) / β + 1)) +
        ((extendedProfileStateBound β q r : ℝ) ^ k *
          ((B : ℝ) * k) + 1) ≤
      (k : ℝ) * (((B : ℝ) * k) ^ 2 *
          (extendedProfileStateBound β q r : ℝ) *
            ((explicitLargeSlotBound β q r : ℝ) / β + 1)) +
        ((extendedProfileStateBound β q r : ℝ) ^ k *
            ((B : ℝ) * k) ^ 2 + ((B : ℝ) * k) ^ 2) := by
      apply add_le_add (le_refl _)
      exact add_le_add
        (mul_le_mul_of_nonneg_left hn_sq hMpow)
        hone_sq
    _ = ((k : ℝ) * (extendedProfileStateBound β q r : ℝ) *
            ((explicitLargeSlotBound β q r : ℝ) / β + 1) +
          (extendedProfileStateBound β q r : ℝ) ^ k + 1) *
        ((B : ℝ) * k) ^ 2 := by ring

/-- For fixed parameters and block width, the exact combined packing
deviation is uniformly sublinear in the exact palette size `B*k`. -/
theorem extendedProfileBlockCombinedDeviation_sublinear
    {L k : ℕ} {rho s omega β q r : ℝ}
    (hβ : 0 < β) (hrho : 0 ≤ rho) (hs : 0 ≤ s)
    (homega0 : 0 < omega) (homega1 : omega ≤ 1) :
    ∀ epsilon : ℝ, 0 < epsilon → ∃ N : ℕ, ∀ B : ℕ,
      N ≤ B * k →
        extendedProfileBlockCombinedDeviation L rho s omega β q r B k ≤
          epsilon * (B * k) := by
  intro epsilon hepsilon
  let A := extendedProfileBlockCombinedMeanCoefficient L rho s omega β q r
  let C0 := extendedProfileBlockCombinedColumnCoefficient k β q r
  have hA : 0 ≤ A :=
    extendedProfileBlockCombinedMeanCoefficient_nonneg
      hrho hs homega0 homega1
  have hC0 : 0 ≤ C0 :=
    extendedProfileBlockCombinedColumnCoefficient_nonneg hβ
  rcases
      FinitePartialResamplingNumerics.packingDeviation_sublinear_of_linear_row_quadratic_column
          hA hC0 epsilon hepsilon with
    ⟨N0, hN0⟩
  refine ⟨max N0 1, ?_⟩
  intro B hn
  let n : ℕ := B * k
  have hN0n : N0 ≤ n := (le_max_left N0 1).trans hn
  have hn1 : 1 ≤ n := (le_max_right N0 1).trans hn
  unfold extendedProfileBlockCombinedDeviation
  rw [← Nat.cast_mul]
  apply hN0 n hN0n
      (extendedProfileBlockCombinedMeanBound L rho s omega β q r B k)
      (extendedProfileBlockCombinedColumnBound B k β q r)
  · rw [extendedProfileBlockCombinedMeanBound_eq_linear]
    exact mul_nonneg hA
      (mul_nonneg (Nat.cast_nonneg B) (Nat.cast_nonneg k))
  · unfold extendedProfileBlockCombinedColumnBound
      extendedProfileCandidateCapacityColumnBound
      extendedProfileBlockVarianceColumnBound
    positivity
  · simpa [A, n] using
      (extendedProfileBlockCombinedMeanBound_eq_linear
        L rho s omega β q r B k).le
  · simpa [C0, n] using
      (extendedProfileBlockCombinedColumnBound_le_quadratic
        (B := B) (k := k) (β := β) (q := q) (r := r) hβ hn1)

end WeightedMultigraph

end

end WeightedEdgeColoring
