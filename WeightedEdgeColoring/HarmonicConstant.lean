import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Topology.Algebra.InfiniteSum.Basic

/-!
# The harmonic bin-packing constant

The manuscript uses the Sylvester sequence

`1, 2, 6, 42, 1806, ...`

and the sum of its reciprocals.  This file gives that constant a concrete
Lean definition.  The indexing starts at zero, so `sylvesterNumber 0 = 1`.
-/

namespace WeightedEdgeColoring

/-- The Sylvester numbers `1, 2, 6, 42, ...`. -/
def sylvesterNumber : ℕ → ℕ
  | 0 => 1
  | n + 1 => sylvesterNumber n * (sylvesterNumber n + 1)

@[simp] theorem sylvesterNumber_zero : sylvesterNumber 0 = 1 := rfl

@[simp] theorem sylvesterNumber_succ (n : ℕ) :
    sylvesterNumber (n + 1) =
      sylvesterNumber n * (sylvesterNumber n + 1) := rfl

theorem sylvesterNumber_pos (n : ℕ) : 0 < sylvesterNumber n := by
  induction n with
  | zero => simp
  | succ n ih =>
      rw [sylvesterNumber_succ]
      exact Nat.mul_pos ih (Nat.succ_pos _)

theorem one_le_sylvesterNumber (n : ℕ) : 1 ≤ sylvesterNumber n :=
  sylvesterNumber_pos n

/-- The Sylvester numbers grow at least geometrically. -/
theorem two_pow_le_sylvesterNumber (n : ℕ) :
    2 ^ n ≤ sylvesterNumber n := by
  induction n with
  | zero => simp
  | succ n ih =>
      rw [sylvesterNumber_succ, pow_succ]
      have hone := one_le_sylvesterNumber n
      nlinarith [Nat.mul_le_mul_left 2 ih]

/-- The reciprocal Sylvester series is summable. -/
theorem summable_inv_sylvesterNumber :
    Summable (fun n : ℕ => (1 : ℝ) / sylvesterNumber n) := by
  apply Summable.of_nonneg_of_le (fun n => by positivity) _ summable_geometric_two
  intro n
  have hpos : (0 : ℝ) < sylvesterNumber n := by
    exact_mod_cast sylvesterNumber_pos n
  have hpowpos : (0 : ℝ) < (((2 ^ n : ℕ) : ℝ)) := by positivity
  have hle : ((2 ^ n : ℕ) : ℝ) ≤ sylvesterNumber n := by
    exact_mod_cast two_pow_le_sylvesterNumber n
  calc
    (1 : ℝ) / sylvesterNumber n ≤ 1 / (2 ^ n : ℕ) := by
      exact one_div_le_one_div_of_le hpowpos hle
    _ = (1 : ℝ) / (2 : ℝ) ^ n := by
      rw [Nat.cast_pow, Nat.cast_ofNat]
    _ = (1 / 2 : ℝ) ^ n := by simp

/-- The classical harmonic bin-packing constant `h∞`. -/
noncomputable def harmonicBinPackingConstant : ℝ :=
  ∑' n : ℕ, (1 : ℝ) / sylvesterNumber n

theorem harmonicBinPackingConstant_nonneg :
    0 ≤ harmonicBinPackingConstant := by
  unfold harmonicBinPackingConstant
  exact tsum_nonneg fun n => by positivity

/-- The reciprocal Sylvester sum is strictly below two. -/
theorem harmonicBinPackingConstant_lt_two :
    harmonicBinPackingConstant < 2 := by
  let f : ℕ → ℝ := fun n => (1 : ℝ) / sylvesterNumber n
  let g : ℕ → ℝ := fun n => (1 / 2 : ℝ) ^ n
  have hf : Summable f := summable_inv_sylvesterNumber
  have hg : Summable g := summable_geometric_two
  have hle : ∀ n, f n ≤ g n := by
    intro n
    have hpowpos : (0 : ℝ) < (((2 ^ n : ℕ) : ℝ)) := by positivity
    have hbound : ((2 ^ n : ℕ) : ℝ) ≤ sylvesterNumber n := by
      exact_mod_cast two_pow_le_sylvesterNumber n
    calc
      f n = (1 : ℝ) / sylvesterNumber n := rfl
      _ ≤ 1 / (2 ^ n : ℕ) :=
        one_div_le_one_div_of_le hpowpos hbound
      _ = g n := by simp [g]
  have hstrict : f 2 < g 2 := by
    norm_num [f, g, sylvesterNumber]
  have htsum : (∑' n, f n) < ∑' n, g n :=
    Summable.tsum_lt_tsum hle hstrict hf hg
  have hgeom : (∑' n, g n) = 2 := by
    change (∑' n : ℕ, (1 / 2 : ℝ) ^ n) = 2
    rw [tsum_geometric_of_norm_lt_one (by norm_num : ‖(1 / 2 : ℝ)‖ < 1)]
    norm_num
  simpa [harmonicBinPackingConstant, f, hgeom] using htsum

/-- The first four terms already put `h∞` strictly above `8/5`. -/
theorem eight_fifths_lt_harmonicBinPackingConstant :
    (8 / 5 : ℝ) < harmonicBinPackingConstant := by
  let f : ℕ → ℝ := fun n => (1 : ℝ) / sylvesterNumber n
  have hsum := summable_inv_sylvesterNumber
  have hpartial :
      (71 / 42 : ℝ) = ∑ n ∈ Finset.range 4, f n := by
    norm_num [f, sylvesterNumber, Finset.sum_range_succ]
  have htailNonneg : 0 ≤ ∑' n : {n // n ∉ Finset.range 4}, f n.1 :=
    tsum_nonneg fun n => by positivity
  have hsplit := hsum.sum_add_tsum_compl (s := Finset.range 4)
  rw [← hpartial] at hsplit
  unfold harmonicBinPackingConstant
  rw [← hsplit]
  have hstrict : (8 / 5 : ℝ) < 71 / 42 := by norm_num
  exact hstrict.trans_le (le_add_of_nonneg_right htailNonneg)

/-- The selection fraction used in the improved general-multigraph bound. -/
noncomputable def harmonicSelectionFraction : ℝ :=
  (2 / 3 : ℝ) * (harmonicBinPackingConstant - 8 / 5)

theorem harmonicSelectionFraction_pos : 0 < harmonicSelectionFraction := by
  unfold harmonicSelectionFraction
  have h := eight_fifths_lt_harmonicBinPackingConstant
  nlinarith

theorem harmonicSelectionFraction_lt_one : harmonicSelectionFraction < 1 := by
  unfold harmonicSelectionFraction
  have h := harmonicBinPackingConstant_lt_two
  nlinarith

theorem harmonicSelectionFraction_lower :
    (19 / 315 : ℝ) ≤ harmonicSelectionFraction := by
  unfold harmonicSelectionFraction
  have h71 : (71 / 42 : ℝ) ≤ harmonicBinPackingConstant := by
    have hsum := summable_inv_sylvesterNumber
    let f : ℕ → ℝ := fun n => (1 : ℝ) / sylvesterNumber n
    have hpartial :
        (71 / 42 : ℝ) = ∑ n ∈ Finset.range 4, f n := by
      norm_num [f, sylvesterNumber, Finset.sum_range_succ]
    have htail : 0 ≤ ∑' n : {n // n ∉ Finset.range 4}, f n.1 :=
      tsum_nonneg fun n => by positivity
    have hsplit := hsum.sum_add_tsum_compl (s := Finset.range 4)
    rw [← hpartial] at hsplit
    unfold harmonicBinPackingConstant
    rw [← hsplit]
    exact le_add_of_nonneg_right htail
  nlinarith

theorem harmonic_selection_coefficient_identity :
    2 + (3 / 2 : ℝ) * harmonicSelectionFraction =
      harmonicBinPackingConstant + 2 / 5 := by
  unfold harmonicSelectionFraction
  ring

end WeightedEdgeColoring
