import WeightedEdgeColoring.SubtwoMixedGraphJointScalarMargin

/-! Numerical room for the actual joint selector in the dyadic slot budget. -/

namespace WeightedEdgeColoring

noncomputable section

namespace WeightedMultigraph

theorem jointProfile_selectedCandidateRate_le_slotTarget
    {tau : ℝ} (htau0 : 0 < tau) (htau1 : tau ≤ 1 / 4) :
    jointProfileRho tau / (1 - jointProfileOmega tau) +
        tau ^ 2 / 4 ≤ 1 - tau / 2 := by
  have hden : 0 < 1 - tau := by linarith
  unfold jointProfileRho jointProfileOmega
  have hpoly : 1 - 2 * tau ≤
      (1 - tau / 2 - tau ^ 2 / 4) * (1 - tau) := by
    nlinarith [sq_nonneg tau, mul_nonneg (sq_nonneg tau) htau0.le]
  have hdiv := (div_le_iff₀ hden).2 hpoly
  linarith

theorem jointProfile_selectedCandidate_bound_le_slotTarget
    {tau scaledDeviation : ℝ}
    (htau0 : 0 < tau) (htau1 : tau ≤ 1 / 4)
    (hdev : scaledDeviation ≤ tau ^ 2 / 4) :
    jointProfileRho tau / (1 - jointProfileOmega tau) +
        scaledDeviation ≤ 1 - tau / 2 := by
  calc
    jointProfileRho tau / (1 - jointProfileOmega tau) +
        scaledDeviation ≤
        jointProfileRho tau / (1 - jointProfileOmega tau) +
          tau ^ 2 / 4 := add_le_add_right hdev _
    _ ≤ 1 - tau / 2 :=
      jointProfile_selectedCandidateRate_le_slotTarget htau0 htau1

theorem jointProfile_selectedTiny_margin
    {tau scaledDeviation : ℝ}
    (htau0 : 0 < tau) (htau1 : tau ≤ 1 / 4)
    (hdev : scaledDeviation ≤ tau ^ 2 / 4) :
    scaledDeviation + 2 * jointProfileBeta tau ≤
      (1 - jointProfileRho tau / (1 - jointProfileOmega tau)) *
        jointProfileR tau :=
  jointProfile_tinyReservoir_margin htau0 htau1 hdev

end WeightedMultigraph

end

end WeightedEdgeColoring
