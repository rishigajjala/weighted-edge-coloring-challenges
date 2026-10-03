import WeightedEdgeColoring.SubtwoMixedGraphReservoirRelativeDecoder
import WeightedEdgeColoring.BoundedMultiplicityJointProfileParameters

/-!
# Joint-profile scalar room for tiny reservoir rounding
-/

namespace WeightedEdgeColoring

noncomputable section

namespace WeightedMultigraph

theorem jointProfile_tinyReservoir_rate_le_one
    {tau : ℝ} (htau0 : 0 < tau) (htau1 : tau ≤ 1 / 4) :
    jointProfileRho tau / (1 - jointProfileOmega tau) ≤ 1 := by
  have hden : 0 < 1 - tau := by linarith
  unfold jointProfileRho jointProfileOmega
  apply (div_le_iff₀ hden).2
  nlinarith

theorem jointProfile_tinyReservoir_margin
    {tau deviation : ℝ}
    (htau0 : 0 < tau) (htau1 : tau ≤ 1 / 4)
    (hdeviation : deviation ≤ tau ^ 2 / 4) :
    deviation + 2 * jointProfileBeta tau ≤
      (1 - jointProfileRho tau / (1 - jointProfileOmega tau)) *
        jointProfileR tau := by
  have hden : 0 < 1 - tau := by linarith
  have hsq : 0 ≤ tau ^ 2 := sq_nonneg tau
  have hgap :
      (1 - (1 - 2 * tau) / (1 - tau)) * tau =
        tau ^ 2 / (1 - tau) := by
    field_simp [ne_of_gt hden]
    <;> ring
  have hdiv : tau ^ 2 ≤ tau ^ 2 / (1 - tau) := by
    apply (le_div_iff₀ hden).2
    have hcube : 0 ≤ tau ^ 2 * tau := mul_nonneg hsq htau0.le
    nlinarith
  unfold jointProfileBeta jointProfileRho jointProfileOmega jointProfileR
  rw [hgap]
  nlinarith

end WeightedMultigraph

end

end WeightedEdgeColoring
