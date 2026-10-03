import WeightedEdgeColoring.HarmonicConstant
import Mathlib.Tactic

/-!
# A rational bound on the harmonic constant and the tiny-edge margin

The tail is bounded by a geometric series after the first five terms.
Thus the strict margin used in the dense-block construction is proved
from the infinite-series definition, not assumed from a decimal value.
-/

open scoped BigOperators

namespace WeightedEdgeColoring.Subtwo

theorem sylvester_shift_ge_geometric (k n : ℕ) :
    sylvesterNumber k * 2 ^ n ≤ sylvesterNumber (n + k) := by
  induction n with
  | zero => simp
  | succ n hn =>
    have hpos := one_le_sylvesterNumber (n + k)
    rw [show n + 1 + k = (n + k) + 1 by omega, sylvesterNumber_succ, pow_succ]
    nlinarith

theorem sylvester_tail_le (k : ℕ) :
    (∑' n : ℕ, (1 : ℝ) / sylvesterNumber (n + k)) ≤ 2 / sylvesterNumber k := by
  have hpos : (0 : ℝ) < sylvesterNumber k := by
    exact_mod_cast sylvesterNumber_pos k
  have hpoint (n : ℕ) :
      (1 : ℝ) / sylvesterNumber (n + k) ≤
        (1 / sylvesterNumber k) * (1 / 2 : ℝ) ^ n := by
    have hb : (sylvesterNumber k : ℝ) * 2 ^ n ≤ sylvesterNumber (n + k) := by
      exact_mod_cast sylvester_shift_ge_geometric k n
    calc
      (1 : ℝ) / sylvesterNumber (n + k) ≤
          1 / ((sylvesterNumber k : ℝ) * 2 ^ n) :=
        one_div_le_one_div_of_le (mul_pos hpos (by positivity)) hb
      _ = (1 / sylvesterNumber k) * (1 / 2 : ℝ) ^ n := by
        simp [div_eq_mul_inv, mul_comm]
  have hs : Summable (fun n : ℕ ↦ (1 : ℝ) / sylvesterNumber (n + k)) :=
    (summable_nat_add_iff k).2 summable_inv_sylvesterNumber
  have hg : Summable (fun n : ℕ ↦ (1 / (sylvesterNumber k : ℝ)) * (1 / 2 : ℝ) ^ n) :=
    summable_geometric_two.mul_left _
  have ht := Summable.tsum_le_tsum hpoint hs hg
  have hgeom : (∑' n : ℕ, (1 / 2 : ℝ) ^ n) = 2 := by
    rw [tsum_geometric_of_norm_lt_one (by norm_num : ‖(1 / 2 : ℝ)‖ < 1)]
    norm_num
  rw [tsum_mul_left, hgeom] at ht
  simpa [div_eq_mul_inv, mul_comm] using ht

theorem harmonic_le_rational_upper :
    harmonicBinPackingConstant ≤ (2759290 / 1631721 : ℝ) := by
  have htail := sylvester_tail_le 5
  have hsplit := summable_inv_sylvesterNumber.sum_add_tsum_nat_add 5
  unfold harmonicBinPackingConstant
  rw [← hsplit]
  calc
    _ ≤ (∑ i ∈ Finset.range 5, (1 : ℝ) / sylvesterNumber i) +
        2 / sylvesterNumber 5 := add_le_add le_rfl htail
    _ = (2759290 / 1631721 : ℝ) := by
      norm_num [Finset.sum_range_succ, sylvesterNumber]

/-- The exact small-item choice in the manuscript leaves a strict positive
margin below `M`, uniformly in the minimum edge weight. -/
theorem harmonic_add_tiny_charge_lt_M {b : ℝ}
    (hb : b ≤ (1 / 10000000 : ℝ)) :
    harmonicBinPackingConstant + b / (1 - b) < (1691031 / 1000000 : ℝ) := by
  have hden : 0 < 1 - b := by linarith
  have hratio : b / (1 - b) ≤ (1 / 9999999 : ℝ) := by
    apply (div_le_iff₀ hden).2
    linarith
  have hh := harmonic_le_rational_upper
  linarith

theorem harmonic_lt_M : harmonicBinPackingConstant < (1691031 / 1000000 : ℝ) := by
  simpa using harmonic_add_tiny_charge_lt_M (b := 0) (by norm_num)

end WeightedEdgeColoring.Subtwo
