import Mathlib.Tactic

/-!
# Exact arithmetic for the reserved-boundary transfer

The matching inequality is an explicit input here. This file verifies
the scalar implication at 1999/1000; it does not assert the matching
polytope theorem or the final graph-wide coloring theorem.
-/

namespace WeightedEdgeColoring.Subtwo.AnalyticBoundary

noncomputable def localBound : ℝ := 157 / 80
noncomputable def degreeBound : ℝ := 16911 / 10000
noncomputable def target : ℝ := 1999 / 1000

/-- The completed square responsible for the strict margin. -/
theorem transfer_square (T : ℝ) :
    (target - localBound) * (8 * degreeBound - 3 * T) -
      (T - 2 * localBound) * (5 * degreeBound - 2 * T) =
        2 * (T - 3283 / 800) ^ 2 + 4423 / 40000000 := by
  norm_num [target, localBound, degreeBound]
  ring

theorem transfer_margin (T : ℝ) (hT : 2 * target ≤ T)
    (hQ : 0 < 5 * degreeBound - 2 * T) :
    (target - localBound) *
        (5 * degreeBound - 2 * T + max 2 (T / 2) - degreeBound) >
      (max 2 (T / 2) - localBound) * (5 * degreeBound - 2 * T) := by
  by_cases hfour : T ≤ 4
  · rw [max_eq_left (by linarith : T / 2 ≤ 2)]
    norm_num [target, localBound, degreeBound] at *
    nlinarith
  · rw [max_eq_right (by linarith : 2 ≤ T / 2)]
    have hs := transfer_square T
    have hspos : 0 < 2 * (T - 3283 / 800) ^ 2 + (4423 / 40000000 : ℝ) := by
      positivity
    nlinarith [hs]

/-- Once the fractional matching estimate has been established, the
local 157/80 bound gives the strict reserved-palette bound 1999/1000. -/
theorem price_transfer (C Z T : ℝ)
    (hT : 2 * target ≤ T) (hQ : 0 < 5 * degreeBound - 2 * T)
    (hC : C ≤ localBound)
    (hmatching : C + (1 + (max 2 (T / 2) - degreeBound) /
      (5 * degreeBound - 2 * T)) * Z ≤ max 2 (T / 2)) :
    C + Z < target := by
  let Q : ℝ := 5 * degreeBound - 2 * T
  let L : ℝ := max 2 (T / 2)
  let k : ℝ := 1 + (L - degreeBound) / Q
  have hQpos : 0 < Q := hQ
  have hL : 2 ≤ L := le_max_left _ _
  have hM : degreeBound < 2 := by norm_num [degreeBound]
  have hk : 1 < k := by
    dsimp [k]
    have hp : 0 < (L - degreeBound) / Q := div_pos (by linarith) hQpos
    linarith
  have hkQ : k * Q = Q + L - degreeBound := by
    dsimp [k]
    field_simp
    ring
  have hmargin := transfer_margin T hT hQ
  change (target - localBound) * (Q + L - degreeBound) >
    (L - localBound) * Q at hmargin
  rw [← hkQ] at hmargin
  have hstrict : L - localBound < (target - localBound) * k := by
    have hrearr : (L - localBound) * Q < ((target - localBound) * k) * Q := by
      nlinarith [hmargin]
    exact (mul_lt_mul_iff_left₀ hQpos).mp hrearr
  have hmatch : C + k * Z ≤ L := hmatching
  have hsmall := mul_nonneg (by linarith : 0 ≤ k - 1) (sub_nonneg.mpr hC)
  by_contra hbad
  have hsum : target ≤ C + Z := le_of_not_gt hbad
  have hmul := mul_le_mul_of_nonneg_left hsum (by linarith : 0 ≤ k)
  nlinarith [hmul, hsmall]

/-- Include the zero-boundary case without dividing by its zero budget. -/
theorem price_transfer_with_zero_boundary (C Z T : ℝ)
    (hT : 2 * target ≤ T) (hQ : 0 ≤ 5 * degreeBound - 2 * T)
    (hC : C ≤ localBound) (hZ : Z ≤ 5 * degreeBound - 2 * T)
    (hmatching : 0 < 5 * degreeBound - 2 * T →
      C + (1 + (max 2 (T / 2) - degreeBound) /
        (5 * degreeBound - 2 * T)) * Z ≤ max 2 (T / 2)) :
    C + Z < target := by
  rcases eq_or_lt_of_le hQ with hz | hpos
  · have hc : localBound < target := by norm_num [localBound, target]
    linarith
  · exact price_transfer C Z T hT hpos hC (hmatching hpos)

end WeightedEdgeColoring.Subtwo.AnalyticBoundary
