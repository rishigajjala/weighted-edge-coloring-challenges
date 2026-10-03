import WeightedEdgeColoring.NatClogRpowStageBound
import WeightedEdgeColoring.KempeGraphMomentBlockConcrete

/-!
# Vanishing accumulated error for the concrete moment block

The one-block selector has scale `B = B₀/n`, linear row parameter, and
quadratic column parameter when `q ≤ C n`.  Combining those explicit bounds
with the logarithmic schedule estimate makes the total selector error vanish.
-/

namespace WeightedEdgeColoring
namespace WeightedMultigraph

open WeightedEdgeColoring.FinitePartialResamplingNumerics

noncomputable section

universe u

theorem eventually_sixteen_clog_mul_momentBlockError_le
    {alpha C L : ℝ} (halpha : 0 < alpha) (hC : 0 < C) (hL : 0 < L) :
    ∀ epsilon : ℝ, 0 < epsilon →
      ∃ N : ℕ, ∀ (G : WeightedMultigraph.{u}) (n q : ℕ), N ≤ n → 0 < n →
        (q : ℝ) ≤ C * n →
        ((16 * Nat.clog 2 n : ℕ) : ℝ) *
          G.momentBlockError alpha L n q ≤ epsilon := by
  let B0 : ℝ := 2 * (L / alpha + L / alpha ^ 2)
  let A : ℝ := (1 / alpha + 1 / alpha ^ 2) / B0
  let C0 : ℝ := 1 + 4 / B0 *
    (1 / alpha + (C + 1) / alpha ^ 2)
  let S : ℝ := 16 * (8 / Real.log 2 + 1)
  have hB0 : 0 < B0 := by dsimp [B0]; positivity
  have hA : 0 ≤ A := by
    dsimp [A, momentBlockM]
    positivity
  have hC0 : 0 ≤ C0 := by
    dsimp [C0]
    positivity
  have hS : 0 ≤ S := by
    dsimp [S]
    have : 0 < Real.log 2 := Real.log_pos (by norm_num)
    positivity
  intro epsilon hepsilon
  rcases eventually_stage_mul_packingDeviation_le_of_inv_linear
      hB0.le hA hC0 hS epsilon hepsilon with ⟨N0, hN0⟩
  refine ⟨max 1 N0, ?_⟩
  intro G n q hnLarge hn hq
  have hn1 : 1 ≤ n := (le_max_left 1 N0).trans hnLarge
  have hN0n : N0 ≤ n := (le_max_right 1 N0).trans hnLarge
  have hnreal : (0 : ℝ) < n := by exact_mod_cast hn
  let B := G.momentBlockB alpha L n
  let R := G.momentBlockM alpha / B
  let Col := G.momentBlockD alpha L n q / B
  have hB : B = B0 / n := by
    dsimp [B, B0, momentBlockB]
  have hBpos : 0 < B := by rw [hB]; positivity
  have hR : R = A * n := by
    dsimp [R, A]
    unfold momentBlockM
    rw [hB]
    field_simp
  have hR0 : 0 ≤ R := by rw [hR]; positivity
  have hCol0 : 0 ≤ Col := by
    dsimp [Col]
    exact div_nonneg (by
      unfold momentBlockD momentBlockB
      positivity) hBpos.le
  have hqplus : (q : ℝ) + 1 ≤ (C + 1) * n := by
    nlinarith [show (1 : ℝ) ≤ n by exact_mod_cast hn1]
  have htail :
      (1 / alpha + ((q : ℝ) + 1) / alpha ^ 2) ≤
        (1 / alpha + (C + 1) / alpha ^ 2) * n := by
    have hnR : (1 : ℝ) ≤ n := by exact_mod_cast hn1
    have hα2 : 0 < alpha ^ 2 := sq_pos_of_pos halpha
    have hdiv := div_le_div_of_nonneg_right hqplus hα2.le
    have hfirst : 1 / alpha ≤ (1 / alpha) * n := by
      calc
        1 / alpha = (1 / alpha) * 1 := by ring
        _ ≤ (1 / alpha) * n :=
          mul_le_mul_of_nonneg_left hnR (by positivity)
    calc
      1 / alpha + ((q : ℝ) + 1) / alpha ^ 2 ≤
          1 / alpha + ((C + 1) * n) / alpha ^ 2 := by
        simpa [add_comm] using add_le_add_left hdiv (1 / alpha)
      _ = 1 / alpha + ((C + 1) / alpha ^ 2) * n := by ring
      _ ≤ (1 / alpha) * n + ((C + 1) / alpha ^ 2) * n := by
        simpa [add_comm] using
          add_le_add_right hfirst (((C + 1) / alpha ^ 2) * n)
      _ = (1 / alpha + (C + 1) / alpha ^ 2) * n := by ring
  have hCol : Col ≤ C0 * (n : ℝ) ^ 2 := by
    have hnR : (1 : ℝ) ≤ n := by exact_mod_cast hn1
    rw [show Col = 1 + 4 / B *
        (1 / alpha + ((q : ℝ) + 1) / alpha ^ 2) by
      dsimp [Col]
      unfold momentBlockD
      field_simp
      ring]
    rw [hB]
    dsimp [C0]
    have hscale : 0 ≤ 4 / (B0 / (n : ℝ)) := by positivity
    calc
      1 + 4 / (B0 / (n : ℝ)) *
          (1 / alpha + ((q : ℝ) + 1) / alpha ^ 2) ≤
        1 + 4 / (B0 / (n : ℝ)) *
          ((1 / alpha + (C + 1) / alpha ^ 2) * n) :=
        by simpa [add_comm] using
          add_le_add_left (mul_le_mul_of_nonneg_left htail hscale) 1
      _ = 1 + (4 / B0 *
          (1 / alpha + (C + 1) / alpha ^ 2)) * (n : ℝ) ^ 2 := by
        field_simp
      _ ≤ (1 + 4 / B0 *
          (1 / alpha + (C + 1) / alpha ^ 2)) * (n : ℝ) ^ 2 := by
        nlinarith [sq_nonneg ((n : ℝ) - 1)]
  have hs : ((16 * Nat.clog 2 n : ℕ) : ℝ) ≤
      S * (n : ℝ) ^ (1 / 8 : ℝ) := by
    simpa [S] using natCast_sixteen_mul_clog_two_le_rpow_eighth hn1
  have hrate := hN0 n hN0n (16 * Nat.clog 2 n) B R Col
    hBpos.le hR0 hCol0 (by rw [hB]) (by rw [hR]) hCol hs
  simpa [momentBlockError, B, R, Col, mul_assoc] using hrate

end

end WeightedMultigraph
end WeightedEdgeColoring
