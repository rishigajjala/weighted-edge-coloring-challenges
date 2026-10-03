import WeightedEdgeColoring.SubtwoProfileRankTable

/-!
# Harmonic charge above physical load

The finite reciprocal induction also bounds the excess of charge over
load. This gives the sharp normal-bin potential without a list of
reciprocal-class cases.
-/

open scoped BigOperators

namespace WeightedEdgeColoring.SubtwoHarmonicRanks

theorem charge_excess_le {w : ℝ} {r : ℕ}
    (hr : 0 < r) (hw : 0 ≤ w) (hcap : w ≤ 1 / (r : ℝ)) :
    harmonicCharge w - w ≤ 1 / ((r : ℝ) * (r + 1)) := by
  have hrR : (0 : ℝ) < r := by exact_mod_cast hr
  have hr1 : (0 : ℝ) < (r : ℝ) + 1 := by positivity
  have hid : 1 / (r : ℝ) - 1 / ((r : ℝ) + 1) =
      1 / ((r : ℝ) * (r + 1)) := by field_simp; ring
  by_cases hlarge : 1 / ((r : ℝ) + 1) < w
  · have hc := harmonicCharge_eq_of_band hr (lt_trans (by positivity) hlarge) hcap hlarge
    rw [← hid, hc]
    linarith
  · have hsmall : w ≤ 1 / ((r : ℝ) + 1) := le_of_not_gt hlarge
    have hc := charge_le_linear (r := r + 1) (by omega) hw (by simpa using hsmall)
    have hc' : harmonicCharge w ≤ ((r : ℝ) + 2) / ((r : ℝ) + 1) * w := by
      simpa [Nat.cast_add, Nat.cast_one, add_assoc] using hc
    have hbound : w / ((r : ℝ) + 1) ≤ 1 / ((r : ℝ) * (r + 1)) := by
      apply (div_le_iff₀ hr1).2
      have heq : (1 / ((r : ℝ) * (r + 1))) * ((r : ℝ) + 1) = 1 / (r : ℝ) := by
        field_simp
      rw [heq]
      exact hcap
    have heq : ((r : ℝ) + 2) / ((r : ℝ) + 1) * w - w = w / ((r : ℝ) + 1) := by
      field_simp
      ring
    linarith

/-- A scaled harmonic charge minus load has a simple cap on each
reciprocal interval. -/
theorem scaled_charge_excess_le {w α : ℝ} {r : ℕ}
    (hr : 0 < r) (hw : 0 ≤ w) (hcap : w ≤ 1 / (r : ℝ)) (hα : 1 ≤ α) :
    α * harmonicCharge w - w ≤ α / r - 1 / ((r : ℝ) + 1) := by
  have hrR : (0 : ℝ) < r := by exact_mod_cast hr
  have hc := charge_le_inv hr hw hcap
  have he := charge_excess_le hr hw hcap
  have hm := mul_le_mul_of_nonneg_left hc (sub_nonneg.mpr hα)
  have hid : (α - 1) * (1 / (r : ℝ)) + 1 / ((r : ℝ) * (r + 1)) =
      α / r - 1 / ((r : ℝ) + 1) := by field_simp; ring
  linarith

/-- At most `k` projections with total load at most `1/r` have total
excess bounded by the next `k` reciprocal terms. -/
theorem sum_charge_excess_le_prefix {ι : Type*} [DecidableEq ι]
    (S : Finset ι) (w : ι → ℝ) (k r : ℕ)
    (hr : 0 < r) (hcard : S.card ≤ k)
    (hnonneg : ∀ i ∈ S, 0 ≤ w i)
    (hload : ∑ i ∈ S, w i ≤ 1 / (r : ℝ)) :
    (∑ i ∈ S, (harmonicCharge (w i) - w i)) ≤ reciprocalPrefix (r * (r + 1)) k := by
  induction k generalizing S r with
  | zero =>
      have hS : S = ∅ := Finset.card_eq_zero.mp (by omega)
      subst S; simp [reciprocalPrefix]
  | succ k ih =>
      have hrR : (0 : ℝ) < r := by exact_mod_cast hr
      by_cases hlarge : ∃ i ∈ S, 1 / ((r : ℝ) + 1) < w i
      · obtain ⟨i, hi, hlarge⟩ := hlarge
        have hwi : w i ≤ 1 / (r : ℝ) := (Finset.single_le_sum hnonneg hi).trans hload
        have hc := charge_excess_le hr (hnonneg i hi) hwi
        have heq := Finset.sum_erase_add S w hi
        have hdiff : 1 / (r : ℝ) - 1 / ((r : ℝ) + 1) =
            1 / ((r : ℝ) * (r + 1)) := by field_simp; ring
        have hload' : ∑ j ∈ S.erase i, w j ≤ 1 / ((r * (r + 1) : ℕ) : ℝ) := by
          push_cast
          rw [← hdiff]
          linarith
        have hrec := ih (S.erase i) (r * (r + 1)) (by positivity)
          (by rw [Finset.card_erase_of_mem hi]; omega)
          (fun j hj => hnonneg j (Finset.mem_of_mem_erase hj)) hload'
        have hsum := Finset.sum_erase_add S (fun j => harmonicCharge (w j) - w j) hi
        rw [reciprocalPrefix]
        push_cast
        push_cast at hrec
        linarith
      · have hsmall : ∀ i ∈ S, w i ≤ 1 / ((r : ℝ) + 1) := by
          intro i hi; exact le_of_not_gt (fun h => hlarge ⟨i, hi, h⟩)
        have hpoint : ∀ i ∈ S, harmonicCharge (w i) - w i ≤ w i / ((r : ℝ) + 1) := by
          intro i hi
          have hc := charge_le_linear (r := r + 1) (by omega) (hnonneg i hi)
            (by simpa using hsmall i hi)
          have hc' : harmonicCharge (w i) ≤ ((r : ℝ) + 2) / ((r : ℝ) + 1) * w i := by
            simpa [Nat.cast_add, Nat.cast_one, add_assoc] using hc
          have hid : ((r : ℝ) + 2) / ((r : ℝ) + 1) * w i - w i =
              w i / ((r : ℝ) + 1) := by field_simp; ring
          linarith
        have hsum := Finset.sum_le_sum hpoint
        rw [← Finset.sum_div] at hsum
        have htotal : (∑ i ∈ S, w i) / ((r : ℝ) + 1) ≤
            1 / ((r * (r + 1) : ℕ) : ℝ) := by
          calc
            _ ≤ (1 / (r : ℝ)) / ((r : ℝ) + 1) :=
              div_le_div_of_nonneg_right hload (by positivity)
            _ = _ := by push_cast; field_simp
        have hp := reciprocalPrefix_nonneg ((r * (r + 1)) * ((r * (r + 1)) + 1)) k
        rw [reciprocalPrefix]
        linarith

theorem sum_charge_excess_le_card_cap {ι : Type*} [DecidableEq ι]
    (S : Finset ι) (w : ι → ℝ) (k r : ℕ)
    (hr : 0 < r) (hcard : S.card ≤ k)
    (hnonneg : ∀ i ∈ S, 0 ≤ w i) (hcap : ∀ i ∈ S, w i ≤ 1 / (r : ℝ)) :
    (∑ i ∈ S, (harmonicCharge (w i) - w i)) ≤ (k : ℝ) / ((r : ℝ) * (r + 1)) := by
  calc
    _ ≤ ∑ _i ∈ S, 1 / ((r : ℝ) * (r + 1)) :=
      Finset.sum_le_sum fun i hi => charge_excess_le hr (hnonneg i hi) (hcap i hi)
    _ = (S.card : ℝ) / ((r : ℝ) * (r + 1)) := by simp [div_eq_mul_inv]
    _ ≤ _ := div_le_div_of_nonneg_right (by exact_mod_cast hcard) (by positivity)

end WeightedEdgeColoring.SubtwoHarmonicRanks
