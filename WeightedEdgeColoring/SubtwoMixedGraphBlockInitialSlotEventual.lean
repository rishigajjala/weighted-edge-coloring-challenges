import WeightedEdgeColoring.SubtwoMixedGraphJointInitialSlotBudget
import WeightedEdgeColoring.SubtwoMixedGraphBlockDecoderScalars

/-! The actual block selector's fixed dyadic choice loss is eventually
absorbed by its initial slot reserve. -/

namespace WeightedEdgeColoring

noncomputable section

namespace WeightedMultigraph

theorem mixedGraph_eventually_blockInitialSlotLoss
    {tau : ℝ} {Ccoef : ℕ}
    (htau : 0 < tau) (htau1 : tau ≤ 1 / 4) :
    ∃ n0 : ℕ, ∀ n : ℕ, n0 ≤ n →
      let m := dyadicSimpleRoot n
      let N := dyadicSimpleQuantizationScale m
      let C := Ccoef * m ^ 20
      C ≤ N ∧ (C : ℝ) + 1 ≤ (tau / 8) * N := by
  obtain ⟨M0, hM0⟩ := Filter.eventually_atTop.1
    (eventually_const_le_pos_mul_nat
      ((Ccoef : ℝ) + 1) (tau / 8) (by positivity))
  refine ⟨max 1 (M0 ^ 20), ?_⟩
  intro n hn
  dsimp only
  let m := dyadicSimpleRoot n
  let N := dyadicSimpleQuantizationScale m
  let C := Ccoef * m ^ 20
  have hMpow : M0 ^ 20 ≤ n := (le_max_right 1 (M0 ^ 20)).trans hn
  have hmM : M0 ≤ m := le_dyadicSimpleRoot_of_pow_le hMpow
  have hm1 : 1 ≤ m := by
    apply le_dyadicSimpleRoot_of_pow_le
    have hn1 : 1 ≤ n := (le_max_left 1 _).trans hn
    simpa using hn1
  have hmR : (1 : ℝ) ≤ m := by exact_mod_cast hm1
  have hm20 : (1 : ℝ) ≤ (m : ℝ) ^ 20 := one_le_pow₀ hmR
  have hm10 : (m : ℝ) ≤ (m : ℝ) ^ 10 := by
    calc
      (m : ℝ) = (m : ℝ) ^ 1 := by ring
      _ ≤ (m : ℝ) ^ 10 := pow_le_pow_right₀ hmR (by omega)
  have hgrowth : (Ccoef : ℝ) + 1 ≤
      (tau / 8) * (m : ℝ) ^ 10 :=
    (hM0 m hmM).trans (mul_le_mul_of_nonneg_left hm10
      (by positivity))
  have hloss : (C : ℝ) + 1 ≤ (tau / 8) * N := by
    dsimp [C, N, dyadicSimpleQuantizationScale]
    push_cast
    calc
      (Ccoef : ℝ) * (m : ℝ) ^ 20 + 1 ≤
          (Ccoef : ℝ) * (m : ℝ) ^ 20 + (m : ℝ) ^ 20 := by
        linarith
      _ = ((Ccoef : ℝ) + 1) * (m : ℝ) ^ 20 := by ring
      _ ≤ ((tau / 8) * (m : ℝ) ^ 10) * (m : ℝ) ^ 20 :=
        mul_le_mul_of_nonneg_right hgrowth (by positivity)
      _ = (tau / 8) * (m : ℝ) ^ 30 := by ring
  have hgamma1 : tau / 8 ≤ 1 := by linarith
  have hCN : C ≤ N := by
    have hreal : (C : ℝ) ≤ N := by
      calc
        (C : ℝ) ≤ (C : ℝ) + 1 := le_add_of_nonneg_right zero_le_one
        _ ≤ (tau / 8) * N := hloss
        _ ≤ 1 * (N : ℝ) :=
          mul_le_mul_of_nonneg_right hgamma1 (Nat.cast_nonneg N)
        _ = N := one_mul _
    exact_mod_cast hreal
  exact ⟨hCN, hloss⟩

end WeightedMultigraph

end
end WeightedEdgeColoring
