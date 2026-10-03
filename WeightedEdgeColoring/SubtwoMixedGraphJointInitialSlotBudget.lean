import WeightedEdgeColoring.SubtwoMixedGraphJointScalarBudget
import WeightedEdgeColoring.BoundedMultiplicityDyadicOuterStructuralScales

/-! Actual joint τ candidate rate fits the dyadic initial slot target. -/

namespace WeightedEdgeColoring

noncomputable section

namespace WeightedMultigraph

theorem jointProfile_selected_initialSlotCaps
    {tau scaledDeviation : ℝ} {N C : ℕ}
    (htau0 : 0 < tau) (htau1 : tau ≤ 1 / 4)
    (hCN : C ≤ N)
    (hloss : (C : ℝ) + 1 ≤ (tau / 8) * N)
    (hdev : scaledDeviation ≤ tau ^ 2 / 4) :
    let S0 := RankThreeOptionSystem.OriginalIterationState.fixedSlackPaddedSlotTarget
      (tau / 8) (N - C)
    (N : ℝ) *
        (jointProfileRho tau / (1 - jointProfileOmega tau) +
          scaledDeviation) ≤ S0 ∧
      (1 - tau / 4) * (N : ℝ) ≤ S0 ∧
      (S0 : ℝ) ≤ (1 - tau / 8) * (N - C) := by
  have hgamma0 : 0 ≤ tau / 8 := by positivity
  have hgammaHalf : tau / 8 ≤ 1 / 2 := by linarith
  have hrate := jointProfile_selectedCandidate_bound_le_slotTarget
    htau0 htau1 hdev
  have hcaps := boundedMultiplicityDyadic_initial_slot_caps
    hgamma0 hgammaHalf hCN hloss (by
      convert hrate using 1 <;> ring)
  dsimp only
  convert hcaps using 1 <;> ring

end WeightedMultigraph

end

end WeightedEdgeColoring
