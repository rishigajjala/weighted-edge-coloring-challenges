import WeightedEdgeColoring.ExtendedProfileBlockAsymptoticBounds
import WeightedEdgeColoring.ExtendedProfileBlockCapacityVarianceSelection

/-!
# Vanishing quadratic error after choosing a fixed block width
-/

namespace WeightedEdgeColoring

noncomputable section

namespace WeightedSimpleGraph

/-- For fixed profile parameters, first choose a sufficiently wide color
block and then a sufficiently large palette.  The selected whole-edge
quadratic budget is at most `epsilon^2` times the palette size. -/
theorem exists_blockWidth_quadraticBound_le
    {rho s omega beta q r epsilon : ℝ}
    (hbeta : 0 < beta) (hrho : 0 ≤ rho) (hs : 0 ≤ s)
    (homega0 : 0 < omega) (homega1 : omega ≤ 1)
    (hepsilon : 0 < epsilon) :
    ∃ k N : ℕ, 0 < k ∧ ∀ B : ℕ, N ≤ B * k →
      extendedProfileBlockQuadraticBound
          rho s omega beta q r B k ≤ epsilon ^ 2 * (B * k) := by
  let C : ℝ := ((explicitLargeSlotBound beta q r : ℝ) + 1) *
    extendedProfileCandidateCapacityScale rho s omega beta q r * (rho * s)
  have hC : 0 ≤ C := by
    dsimp [C]
    exact mul_nonneg
      (mul_nonneg (by positivity)
        (extendedProfileCandidateCapacityScale_nonneg hrho hs))
      (mul_nonneg hrho hs)
  obtain ⟨k, hk⟩ := exists_nat_gt (2 * C / epsilon ^ 2)
  have hkpos : 0 < k := by
    by_contra hk0
    have : k = 0 := Nat.eq_zero_of_not_pos hk0
    subst k
    norm_num at hk ⊢
    have heps2 : 0 ≤ epsilon ^ 2 := sq_nonneg epsilon
    exact (not_lt_of_ge (div_nonneg (mul_nonneg (by norm_num) hC) heps2)) hk
  let A : ℝ := extendedProfileBlockVarianceAmplitude rho s omega beta q r
  let epsD : ℝ := epsilon ^ 2 / (2 * (1 + (k + 1) * A ^ 2))
  have hepsD : 0 < epsD := by
    dsimp [epsD]
    positivity
  obtain ⟨N, hN⟩ := extendedProfileBlockCombinedDeviation_sublinear
    (k := k) (rho := rho) (s := s) (omega := omega) (β := beta)
    (q := q) (r := r) hbeta hrho hs homega0 homega1 epsD hepsD
  refine ⟨k, N, hkpos, ?_⟩
  intro B hlarge
  have hkR : 2 * C / epsilon ^ 2 < (k : ℝ) := by exact_mod_cast hk
  have hlead : (B : ℝ) * C ≤ epsilon ^ 2 * (B * k : ℕ) / 2 := by
    have hCk : 2 * C ≤ epsilon ^ 2 * k := by
      have heps2 : 0 < epsilon ^ 2 := sq_pos_of_pos hepsilon
      simpa [mul_comm] using ((div_lt_iff₀ heps2).mp hkR).le
    push_cast
    have hB0R : (0 : ℝ) ≤ B := by positivity
    nlinarith [mul_le_mul_of_nonneg_left hCk hB0R]
  have hdev := hN B hlarge
  have herr :
      (k + 1 : ℕ) * A ^ 2 *
          extendedProfileBlockCombinedDeviation rho s omega beta q r B k ≤
        epsilon ^ 2 * (B * k : ℕ) / 2 := by
    have hcoef0 : 0 ≤ ((k + 1 : ℕ) : ℝ) * A ^ 2 := by positivity
    have hscaled := mul_le_mul_of_nonneg_left hdev hcoef0
    have hratio :
        ((k + 1 : ℕ) : ℝ) * A ^ 2 * epsD ≤ epsilon ^ 2 / 2 := by
      dsimp [epsD]
      have hden2 : 0 < 2 *
          (1 + ((k + 1 : ℕ) : ℝ) * A ^ 2) := by positivity
      rw [← mul_div_assoc]
      push_cast at hden2 ⊢
      apply (div_le_iff₀ hden2).2
      nlinarith [sq_nonneg A]
    calc
      _ ≤ (((k + 1 : ℕ) : ℝ) * A ^ 2 * epsD) * (B * k : ℕ) := by
        calc
          _ ≤ ((k + 1 : ℕ) * A ^ 2 * (epsD * ((B : ℝ) * k))) := hscaled
          _ = (((k + 1 : ℕ) : ℝ) * A ^ 2 * epsD) *
              (B * k : ℕ) := by push_cast; ring
      _ ≤ (epsilon ^ 2 / 2) * (B * k : ℕ) := by gcongr
      _ = epsilon ^ 2 * (B * k : ℕ) / 2 := by ring
  unfold extendedProfileBlockQuadraticBound
  dsimp [C, A] at hlead herr
  push_cast at hlead herr ⊢
  linarith

end WeightedSimpleGraph
end
end WeightedEdgeColoring
