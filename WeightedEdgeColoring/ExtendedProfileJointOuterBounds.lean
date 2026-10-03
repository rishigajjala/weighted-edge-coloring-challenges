import WeightedEdgeColoring.ExtendedProfileBlockJointFeasibility
import WeightedEdgeColoring.ExtendedProfileBlockQuadraticAsymptotic

/-!
# Outer bounds for the explicit joint-profile parameters
-/

namespace WeightedEdgeColoring

noncomputable section

namespace WeightedSimpleGraph

/-- The ordinary normalized slot load is eventually below `1-tau/2`.
The leading ratio is at most `1-tau`; half of that slack pays the selector
deviation. -/
theorem jointProfile_ordinaryRate_eventually
    {k : ℕ} {tau : ℝ} (hk : 0 < k)
    (htau0 : 0 < tau) (htau1 : tau ≤ 1 / 4) :
    ∃ N : ℕ, ∀ B : ℕ, N ≤ B * k →
      jointProfileRho tau /
            extendedProfileSmoothingKappa (jointProfileOmega tau)
              (jointProfileBeta tau) (jointProfileQ tau) (jointProfileR tau) +
          extendedProfileCandidateCapacityScale
              (jointProfileRho tau) (jointProfileS tau)
              (jointProfileOmega tau) (jointProfileBeta tau)
              (jointProfileQ tau) (jointProfileR tau) /
            ((B * k : ℕ) : ℝ) *
              extendedProfileBlockCombinedDeviation
                (jointProfileRho tau) (jointProfileS tau)
                (jointProfileOmega tau) (jointProfileBeta tau)
                (jointProfileQ tau) (jointProfileR tau) B k ≤
        1 - tau / 2 := by
  rcases jointProfile_parameters htau0 htau1 with
    ⟨hs, hbeta, hq, hr, homega0, homega1, hleft, hr1,
      hrho, hrhoKappa, hfraction⟩
  let scale := extendedProfileCandidateCapacityScale
    (jointProfileRho tau) (jointProfileS tau) (jointProfileOmega tau)
    (jointProfileBeta tau) (jointProfileQ tau) (jointProfileR tau)
  have hscale : 0 < scale :=
    extendedProfileCandidateCapacityScale_pos hrho hs homega0
  have heps : 0 < tau / (2 * scale) := by positivity
  obtain ⟨N0, hN0⟩ := extendedProfileBlockCombinedDeviation_sublinear
    (k := k) (rho := jointProfileRho tau) (s := jointProfileS tau)
    (omega := jointProfileOmega tau) (β := jointProfileBeta tau)
    (q := jointProfileQ tau) (r := jointProfileR tau)
    hbeta hrho.le hs.le homega0 homega1 (tau / (2 * scale)) heps
  refine ⟨max N0 1, ?_⟩
  intro B hB
  have hn : 0 < B * k := Nat.zero_lt_of_lt ((le_max_right N0 1).trans hB)
  have hdev := hN0 B ((le_max_left N0 1).trans hB)
  have hdev' :
      extendedProfileBlockCombinedDeviation
          (jointProfileRho tau) (jointProfileS tau) (jointProfileOmega tau)
          (jointProfileBeta tau) (jointProfileQ tau) (jointProfileR tau) B k ≤
        tau / (2 * scale) * ((B * k : ℕ) : ℝ) := by
    convert hdev using 1 <;> push_cast <;> ring
  have hnR : (0 : ℝ) < (B * k : ℕ) := by exact_mod_cast hn
  have herror : scale / ((B * k : ℕ) : ℝ) *
      extendedProfileBlockCombinedDeviation
        (jointProfileRho tau) (jointProfileS tau) (jointProfileOmega tau)
        (jointProfileBeta tau) (jointProfileQ tau) (jointProfileR tau) B k ≤
      tau / 2 := by
    calc
      _ ≤ scale / ((B * k : ℕ) : ℝ) *
          (tau / (2 * scale) * (B * k : ℕ)) := by
        exact mul_le_mul_of_nonneg_left hdev' (by positivity)
      _ = tau / 2 := by
        field_simp [hscale.ne', hnR.ne']
  have hleading : jointProfileRho tau /
        extendedProfileSmoothingKappa (jointProfileOmega tau)
          (jointProfileBeta tau) (jointProfileQ tau) (jointProfileR tau) ≤
      1 - tau := by linarith
  change _ + scale / ((B * k : ℕ) : ℝ) * _ ≤ _
  linarith

/-- For the explicit parameter family, a fixed block width and a large
enough exact-multiple palette make the decoder variance at most
`epsilon^2` times the palette. -/
theorem exists_jointProfile_blockWidth_quadraticBound_le
    {tau epsilon : ℝ}
    (htau0 : 0 < tau) (htau1 : tau ≤ 1 / 4)
    (hepsilon : 0 < epsilon) :
    ∃ k N : ℕ, 0 < k ∧ ∀ B : ℕ, N ≤ B * k →
      extendedProfileBlockQuadraticBound
          (jointProfileRho tau) (jointProfileS tau) (jointProfileOmega tau)
          (jointProfileBeta tau) (jointProfileQ tau) (jointProfileR tau)
          B k ≤ epsilon ^ 2 * (B * k) := by
  rcases jointProfile_parameters htau0 htau1 with
    ⟨hs, hbeta, hq, hr, homega0, homega1, hleft, hr1,
      hrho, hrhoKappa, hfraction⟩
  exact exists_blockWidth_quadraticBound_le hbeta hrho.le hs.le
    homega0 homega1 hepsilon

end WeightedSimpleGraph
end
end WeightedEdgeColoring
