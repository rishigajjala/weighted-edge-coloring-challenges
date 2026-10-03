import WeightedEdgeColoring.MultigraphExtendedProfileBlockAsymptoticBounds

namespace WeightedEdgeColoring

noncomputable section

namespace WeightedMultigraph

def jointProfileS (tau : ℝ) : ℝ := 1 - 2 * tau

def jointProfileBeta (tau : ℝ) : ℝ := tau ^ 2 / 16

def jointProfileQ (tau : ℝ) : ℝ := tau

def jointProfileR (tau : ℝ) : ℝ := tau

def jointProfileOmega (tau : ℝ) : ℝ := tau

def jointProfileRho (tau : ℝ) : ℝ := 1 - 2 * tau

theorem jointProfile_parameters
    {tau : ℝ} (htau0 : 0 < tau) (htau1 : tau ≤ 1 / 4) :
    0 < jointProfileS tau ∧
      0 < jointProfileBeta tau ∧
      0 < jointProfileQ tau ∧
      0 < jointProfileR tau ∧
      0 < jointProfileOmega tau ∧ jointProfileOmega tau ≤ 1 ∧
      0 ≤ 1 - jointProfileS tau *
        (1 + jointProfileQ tau + jointProfileR tau) ∧
      jointProfileR tau ≤ 1 ∧
      0 < jointProfileRho tau ∧
      jointProfileRho tau ≤
        extendedProfileSmoothingKappa (jointProfileOmega tau)
          (jointProfileBeta tau) (jointProfileQ tau) (jointProfileR tau) ∧
      tau ≤ 1 - jointProfileRho tau /
          extendedProfileSmoothingKappa (jointProfileOmega tau)
            (jointProfileBeta tau) (jointProfileQ tau) (jointProfileR tau) := by
  let stateCount : ℝ := extendedProfileStateBound
    (jointProfileBeta tau) (jointProfileQ tau) (jointProfileR tau)
  let kappa := extendedProfileSmoothingKappa (jointProfileOmega tau)
    (jointProfileBeta tau) (jointProfileQ tau) (jointProfileR tau)
  have hstateNat : 1 ≤ extendedProfileStateBound
      (jointProfileBeta tau) (jointProfileQ tau) (jointProfileR tau) := by
    unfold extendedProfileStateBound
    omega
  have hstate : (1 : ℝ) ≤ stateCount := by
    dsimp [stateCount]
    exact_mod_cast hstateNat
  have hstate0 : 0 < stateCount := zero_lt_one.trans_le hstate
  have htauDiv0 : 0 ≤ tau / stateCount :=
    div_nonneg htau0.le hstate0.le
  have htauDivLe : tau / stateCount ≤ tau := by
    apply (div_le_iff₀ hstate0).2
    have hmul := mul_nonneg htau0.le (sub_nonneg.mpr hstate)
    nlinarith
  have homega0 : 0 < jointProfileOmega tau := by
    simpa [jointProfileOmega] using htau0
  have homega1 : jointProfileOmega tau ≤ 1 := by
    unfold jointProfileOmega
    linarith
  have hkappa0 : 0 < kappa := by
    exact extendedProfileSmoothingKappa_pos homega0 homega1
  have hkappaFormula : kappa = 1 - tau + tau / stateCount := by
    simp [kappa, extendedProfileSmoothingKappa,
      extendedProfileSmoothingDelta, jointProfileOmega, stateCount]
  have hkappa1 : kappa ≤ 1 := by
    rw [hkappaFormula]
    linarith
  have hrhoKappa : jointProfileRho tau ≤ kappa := by
    rw [hkappaFormula]
    unfold jointProfileRho
    linarith
  have hgap : tau ≤ kappa - jointProfileRho tau := by
    rw [hkappaFormula]
    unfold jointProfileRho
    linarith
  have hfraction : tau ≤ 1 - jointProfileRho tau / kappa := by
    have hrewrite : 1 - jointProfileRho tau / kappa =
        (kappa - jointProfileRho tau) / kappa := by
      field_simp [hkappa0.ne']
      <;> ring
    rw [hrewrite]
    apply (le_div_iff₀ hkappa0).2
    calc
      tau * kappa ≤ tau * 1 :=
        mul_le_mul_of_nonneg_left hkappa1 htau0.le
      _ = tau := by ring
      _ ≤ kappa - jointProfileRho tau := hgap
  refine ⟨?_, ?_, htau0, htau0, homega0, homega1, ?_, ?_, ?_, ?_, ?_⟩
  · unfold jointProfileS
    linarith
  · unfold jointProfileBeta
    positivity
  · unfold jointProfileS jointProfileQ jointProfileR
    nlinarith [sq_nonneg tau]
  · unfold jointProfileR
    linarith
  · unfold jointProfileRho
    linarith
  · simpa [kappa] using hrhoKappa
  · simpa [kappa] using hfraction

end WeightedMultigraph
end
end WeightedEdgeColoring
