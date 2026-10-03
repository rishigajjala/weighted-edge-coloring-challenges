import WeightedEdgeColoring.HarmonicBinCharge

/-!
# The scalar calculation for the discounted harmonic charge

The general multigraph argument discounts the harmonic charge on the two
weight ranges `(1/2, 3/5]` and `(1/3, 2/5]`.  Its six-case one-bin estimate
has the envelope `discountedChargeEnvelope` below.  This file proves the
exact calculation at the manuscript's choice

`t* = (2/3) * (h∞ - 8/5)`.

The combinatorial statement that the charge of a unit bin is bounded by this
envelope is kept separate from this scalar calculation.
-/

namespace WeightedEdgeColoring

/-- Whether a weight belongs to one of the two ranges whose harmonic charge
is discounted in the general multigraph proof. -/
def inDiscountedWeightRanges (w : ℝ) : Prop :=
  ((1 / 2 : ℝ) < w ∧ w ≤ 3 / 5) ∨
    ((1 / 3 : ℝ) < w ∧ w ≤ 2 / 5)

/-- Harmonic charge after discounting the two compatible weight ranges by a
fraction `t`. -/
noncomputable def discountedHarmonicCharge (t w : ℝ) : ℝ :=
  by
    classical
    exact if inDiscountedWeightRanges w then
      (1 - t) * harmonicCharge w
    else
      harmonicCharge w

theorem discountedHarmonicCharge_nonneg {t w : ℝ} (ht : t ≤ 1) :
    0 ≤ discountedHarmonicCharge t w := by
  classical
  unfold discountedHarmonicCharge
  split_ifs
  · exact mul_nonneg (sub_nonneg.mpr ht) (harmonicCharge_nonneg w)
  · exact harmonicCharge_nonneg w

theorem discountedHarmonicCharge_le_harmonicCharge {t w : ℝ}
    (ht : 0 ≤ t) :
    discountedHarmonicCharge t w ≤ harmonicCharge w := by
  classical
  unfold discountedHarmonicCharge
  split_ifs
  · have hfactor : (1 - t : ℝ) ≤ 1 := sub_le_self 1 ht
    simpa using
      (mul_le_mul_of_nonneg_right hfactor (harmonicCharge_nonneg w))
  · exact le_rfl

/-- An item in the upper discounted range has harmonic charge one. -/
theorem discountedHarmonicCharge_eq_one_minus_of_upper_range
    {t w : ℝ} (hwLower : (1 / 2 : ℝ) < w)
    (hwUpper : w ≤ 3 / 5) :
    discountedHarmonicCharge t w = 1 - t := by
  have hwPos : 0 < w := lt_trans (by norm_num) hwLower
  have hwOne : w ≤ (1 : ℝ) := hwUpper.trans (by norm_num)
  have hwOne' : w ≤ (1 : ℝ) / (1 : ℕ) := by
    norm_num
    exact hwOne
  have hwLower' : (1 : ℝ) / ((1 : ℕ) + 1) < w := by
    norm_num
    exact hwLower
  have hcharge : harmonicCharge w = 1 := by
    simpa using
      (harmonicCharge_eq_of_band (w := w) (r := 1) (by norm_num)
        hwPos hwOne' hwLower')
  have hrange : inDiscountedWeightRanges w :=
    Or.inl ⟨hwLower, hwUpper⟩
  classical
  simp [discountedHarmonicCharge, hrange, hcharge]

/-- An item in the lower discounted range has harmonic charge one half. -/
theorem discountedHarmonicCharge_eq_half_one_minus_of_lower_range
    {t w : ℝ} (hwLower : (1 / 3 : ℝ) < w)
    (hwUpper : w ≤ 2 / 5) :
    discountedHarmonicCharge t w = (1 - t) / 2 := by
  have hwPos : 0 < w := lt_trans (by norm_num) hwLower
  have hwHalf : w ≤ (1 / 2 : ℝ) := hwUpper.trans (by norm_num)
  have hwHalf' : w ≤ (1 : ℝ) / (2 : ℕ) := by
    norm_num
    exact hwHalf
  have hwLower' : (1 : ℝ) / ((2 : ℕ) + 1) < w := by
    norm_num
    exact hwLower
  have hcharge : harmonicCharge w = (1 / 2 : ℝ) := by
    simpa using
      (harmonicCharge_eq_of_band (w := w) (r := 2) (by norm_num)
        hwPos hwHalf' hwLower')
  have hrange : inDiscountedWeightRanges w :=
    Or.inr ⟨hwLower, hwUpper⟩
  classical
  rw [discountedHarmonicCharge]
  simp only [if_pos hrange, hcharge]
  ring

/-- The six scalar bounds arising from the six cases of the one-bin proof. -/
noncomputable def discountedChargeEnvelope (t : ℝ) : ℝ :=
  max (3 / 2 : ℝ)
    (max (79 / 48 - t)
      (max (harmonicBinPackingConstant - (3 / 2) * t)
        (max (161 / 100 - t)
          (max (23 / 15) (707 / 450 - (1 / 2) * t)))))

theorem discounted_charge_term_one_le_envelope (t : ℝ) :
    (3 / 2 : ℝ) ≤ discountedChargeEnvelope t := by
  simp [discountedChargeEnvelope]

theorem discounted_charge_term_two_le_envelope (t : ℝ) :
    (79 / 48 : ℝ) - t ≤ discountedChargeEnvelope t := by
  simp [discountedChargeEnvelope]

theorem discounted_charge_term_three_le_envelope (t : ℝ) :
    harmonicBinPackingConstant - (3 / 2 : ℝ) * t ≤
      discountedChargeEnvelope t := by
  simp [discountedChargeEnvelope]

theorem discounted_charge_term_four_le_envelope (t : ℝ) :
    (161 / 100 : ℝ) - t ≤ discountedChargeEnvelope t := by
  simp [discountedChargeEnvelope]

theorem discounted_charge_term_five_le_envelope (t : ℝ) :
    (23 / 15 : ℝ) ≤ discountedChargeEnvelope t := by
  simp [discountedChargeEnvelope]

theorem discounted_charge_term_six_le_envelope (t : ℝ) :
    (707 / 450 : ℝ) - (1 / 2) * t ≤
      discountedChargeEnvelope t := by
  simp [discountedChargeEnvelope]

/-- Linear small-item estimate for the discounted charge. -/
theorem discountedHarmonicCharge_sum_le_mul_weight
    {ι : Type*} [DecidableEq ι] (S : Finset ι) (w : ι → ℝ)
    (t : ℝ) (j : ℕ) (ht : 0 ≤ t) (hj : 0 < j)
    (hpos : ∀ i ∈ S, 0 < w i)
    (hsmall : ∀ i ∈ S, w i ≤ (1 : ℝ) / j) :
    ∑ i ∈ S, discountedHarmonicCharge t (w i) ≤
      (((j + 1 : ℕ) : ℝ) / j) * ∑ i ∈ S, w i := by
  calc
    ∑ i ∈ S, discountedHarmonicCharge t (w i) ≤
        ∑ i ∈ S, harmonicCharge (w i) := by
      exact Finset.sum_le_sum fun i _ =>
        discountedHarmonicCharge_le_harmonicCharge ht
    _ ≤ ∑ i ∈ S, (((j + 1 : ℕ) : ℝ) / j) * w i := by
      exact Finset.sum_le_sum fun i hi =>
        harmonicCharge_le_mul_weight hj (hpos i hi) (hsmall i hi)
    _ = (((j + 1 : ℕ) : ℝ) / j) * ∑ i ∈ S, w i := by
      rw [Finset.mul_sum]

/-- The discounted charge inherits the exact harmonic tail bound below
load `1/6`. -/
theorem discountedHarmonicCharge_sum_le_tail_six
    {ι : Type*} [DecidableEq ι] (S : Finset ι) (w : ι → ℝ)
    (t : ℝ) (ht : 0 ≤ t)
    (hpos : ∀ i ∈ S, 0 < w i)
    (hload : ∑ i ∈ S, w i ≤ (1 / 6 : ℝ)) :
    ∑ i ∈ S, discountedHarmonicCharge t (w i) ≤
      harmonicBinPackingConstant - (3 / 2 : ℝ) := by
  calc
    ∑ i ∈ S, discountedHarmonicCharge t (w i) ≤
        ∑ i ∈ S, harmonicCharge (w i) := by
      exact Finset.sum_le_sum fun i _ =>
        discountedHarmonicCharge_le_harmonicCharge ht
    _ ≤ harmonicBinPackingConstant - (3 / 2 : ℝ) :=
      harmonicCharge_sum_le_tail_six S w hpos hload

private theorem positive_term_le_sum
    {ι : Type*} [DecidableEq ι] {S : Finset ι} {w : ι → ℝ}
    (hpos : ∀ i ∈ S, 0 < w i) {i : ι} (hi : i ∈ S) :
    w i ≤ ∑ j ∈ S, w j :=
  Finset.single_le_sum (fun j hj => (hpos j hj).le) hi

/-- Case 1 of the six-case estimate: all items have weight at most one half. -/
theorem discountedHarmonicCharge_sum_le_three_halves
    {ι : Type*} [DecidableEq ι] (S : Finset ι) (w : ι → ℝ)
    (t : ℝ) (ht : 0 ≤ t)
    (hpos : ∀ i ∈ S, 0 < w i)
    (hload : ∑ i ∈ S, w i ≤ 1)
    (hsmall : ∀ i ∈ S, w i ≤ (1 / 2 : ℝ)) :
    ∑ i ∈ S, discountedHarmonicCharge t (w i) ≤ 3 / 2 := by
  have hlinear := discountedHarmonicCharge_sum_le_mul_weight
    S w t 2 ht (by norm_num) hpos (by simpa using hsmall)
  norm_num only [Nat.cast_ofNat, Nat.cast_add, Nat.cast_one] at hlinear
  nlinarith

/-- Case 2 of the six-case estimate: the unique item above one half is in
the upper discounted range, and every other item is at most one third. -/
theorem discountedHarmonicCharge_sum_upper_heavy_small_remainder
    {ι : Type*} [DecidableEq ι] (S : Finset ι) (w : ι → ℝ)
    (t : ℝ) (ht : 0 ≤ t) {h : ι}
    (hpos : ∀ i ∈ S, 0 < w i)
    (hload : ∑ i ∈ S, w i ≤ 1)
    (hh : h ∈ S) (hhLower : (1 / 2 : ℝ) < w h)
    (hhUpper : w h ≤ 3 / 5)
    (hrestSmall : ∀ i ∈ S.erase h, w i ≤ (1 / 3 : ℝ)) :
    ∑ i ∈ S, discountedHarmonicCharge t (w i) ≤
      (79 / 48 : ℝ) - t := by
  classical
  have hposRest : ∀ i ∈ S.erase h, 0 < w i := by
    intro i hi
    exact hpos i (Finset.mem_of_mem_erase hi)
  have hsplitLoad :
      (∑ i ∈ S.erase h, w i) + w h = ∑ i ∈ S, w i :=
    Finset.sum_erase_add S w hh
  have hrestLoad : ∑ i ∈ S.erase h, w i < (1 / 2 : ℝ) := by
    linarith
  have hrestCharge :
      ∑ i ∈ S.erase h, discountedHarmonicCharge t (w i) ≤
        (31 / 48 : ℝ) := by
    by_cases hquarter : ∀ i ∈ S.erase h, w i ≤ (1 / 4 : ℝ)
    · have hlinear := discountedHarmonicCharge_sum_le_mul_weight
        (S.erase h) w t 4 ht (by norm_num) hposRest (by simpa using hquarter)
      norm_num only [Nat.cast_ofNat, Nat.cast_add, Nat.cast_one] at hlinear
      nlinarith
    · simp only [not_forall, not_le] at hquarter
      obtain ⟨r, hrMem, hrLower⟩ := hquarter
      have hrUpper : w r ≤ (1 / 3 : ℝ) := hrestSmall r hrMem
      have hrChargeEq : harmonicCharge (w r) = (1 / 3 : ℝ) := by
        have hrUpper' : w r ≤ (1 : ℝ) / (3 : ℕ) := by
          norm_num
          exact hrUpper
        have hrLower' : (1 : ℝ) / ((3 : ℕ) + 1) < w r := by
          norm_num
          exact hrLower
        simpa using
          (harmonicCharge_eq_of_band (w := w r) (r := 3) (by norm_num)
            (hposRest r hrMem) hrUpper' hrLower')
      have hrCharge : discountedHarmonicCharge t (w r) ≤ (1 / 3 : ℝ) := by
        rw [← hrChargeEq]
        exact discountedHarmonicCharge_le_harmonicCharge ht
      have hposTail :
          ∀ i ∈ (S.erase h).erase r, 0 < w i := by
        intro i hi
        exact hposRest i (Finset.mem_of_mem_erase hi)
      have hsplitTail :
          (∑ i ∈ (S.erase h).erase r, w i) + w r =
            ∑ i ∈ S.erase h, w i :=
        Finset.sum_erase_add (S.erase h) w hrMem
      have htailLoad :
          ∑ i ∈ (S.erase h).erase r, w i < (1 / 4 : ℝ) := by
        linarith
      have htailSmall :
          ∀ i ∈ (S.erase h).erase r, w i ≤ (1 : ℝ) / (4 : ℕ) := by
        intro i hi
        have hterm := positive_term_le_sum hposTail hi
        norm_num
        linarith
      have htailCharge := discountedHarmonicCharge_sum_le_mul_weight
        ((S.erase h).erase r) w t 4 ht (by norm_num) hposTail htailSmall
      norm_num only [Nat.cast_ofNat, Nat.cast_add, Nat.cast_one] at htailCharge
      have hsplitCharge :
          (∑ i ∈ (S.erase h).erase r,
              discountedHarmonicCharge t (w i)) +
              discountedHarmonicCharge t (w r) =
            ∑ i ∈ S.erase h, discountedHarmonicCharge t (w i) :=
        Finset.sum_erase_add (S.erase h)
          (fun i => discountedHarmonicCharge t (w i)) hrMem
      linarith
  have hhCharge :=
    discountedHarmonicCharge_eq_one_minus_of_upper_range
      (t := t) hhLower hhUpper
  have hsplitCharge :
      (∑ i ∈ S.erase h, discountedHarmonicCharge t (w i)) +
          discountedHarmonicCharge t (w h) =
        ∑ i ∈ S, discountedHarmonicCharge t (w i) :=
    Finset.sum_erase_add S (fun i => discountedHarmonicCharge t (w i)) hh
  linarith

/-- Case 3 of the six-case estimate: an upper-range item is accompanied by a
lower-range item. -/
theorem discountedHarmonicCharge_sum_two_discounted_items
    {ι : Type*} [DecidableEq ι] (S : Finset ι) (w : ι → ℝ)
    (t : ℝ) (ht : 0 ≤ t) {h r : ι}
    (hpos : ∀ i ∈ S, 0 < w i)
    (hload : ∑ i ∈ S, w i ≤ 1)
    (hh : h ∈ S) (hr : r ∈ S.erase h)
    (hhLower : (1 / 2 : ℝ) < w h) (hhUpper : w h ≤ 3 / 5)
    (hrLower : (1 / 3 : ℝ) < w r) (hrUpper : w r ≤ 2 / 5) :
    ∑ i ∈ S, discountedHarmonicCharge t (w i) ≤
      harmonicBinPackingConstant - (3 / 2 : ℝ) * t := by
  classical
  have hposRest : ∀ i ∈ S.erase h, 0 < w i := by
    intro i hi
    exact hpos i (Finset.mem_of_mem_erase hi)
  have hposTail : ∀ i ∈ (S.erase h).erase r, 0 < w i := by
    intro i hi
    exact hposRest i (Finset.mem_of_mem_erase hi)
  have hsplitLoad :
      (∑ i ∈ S.erase h, w i) + w h = ∑ i ∈ S, w i :=
    Finset.sum_erase_add S w hh
  have hsplitTail :
      (∑ i ∈ (S.erase h).erase r, w i) + w r =
        ∑ i ∈ S.erase h, w i :=
    Finset.sum_erase_add (S.erase h) w hr
  have htailLoad :
      ∑ i ∈ (S.erase h).erase r, w i ≤ (1 / 6 : ℝ) := by
    linarith
  have htailCharge := discountedHarmonicCharge_sum_le_tail_six
    ((S.erase h).erase r) w t ht hposTail htailLoad
  have hhCharge :=
    discountedHarmonicCharge_eq_one_minus_of_upper_range
      (t := t) hhLower hhUpper
  have hrCharge :=
    discountedHarmonicCharge_eq_half_one_minus_of_lower_range
      (t := t) hrLower hrUpper
  have hsplitChargeH :
      (∑ i ∈ S.erase h, discountedHarmonicCharge t (w i)) +
          discountedHarmonicCharge t (w h) =
        ∑ i ∈ S, discountedHarmonicCharge t (w i) :=
    Finset.sum_erase_add S (fun i => discountedHarmonicCharge t (w i)) hh
  have hsplitChargeR :
      (∑ i ∈ (S.erase h).erase r,
          discountedHarmonicCharge t (w i)) +
          discountedHarmonicCharge t (w r) =
        ∑ i ∈ S.erase h, discountedHarmonicCharge t (w i) :=
    Finset.sum_erase_add (S.erase h)
      (fun i => discountedHarmonicCharge t (w i)) hr
  linarith

/-- Case 4 of the six-case estimate: an upper-range item is accompanied by
an item above `2/5`. -/
theorem discountedHarmonicCharge_sum_upper_heavy_large_companion
    {ι : Type*} [DecidableEq ι] (S : Finset ι) (w : ι → ℝ)
    (t : ℝ) (ht : 0 ≤ t) {h r : ι}
    (hpos : ∀ i ∈ S, 0 < w i)
    (hload : ∑ i ∈ S, w i ≤ 1)
    (hh : h ∈ S) (hr : r ∈ S.erase h)
    (hhLower : (1 / 2 : ℝ) < w h) (hhUpper : w h ≤ 3 / 5)
    (hrLower : (2 / 5 : ℝ) < w r) :
    ∑ i ∈ S, discountedHarmonicCharge t (w i) ≤
      (161 / 100 : ℝ) - t := by
  classical
  have hposRest : ∀ i ∈ S.erase h, 0 < w i := by
    intro i hi
    exact hpos i (Finset.mem_of_mem_erase hi)
  have hposTail : ∀ i ∈ (S.erase h).erase r, 0 < w i := by
    intro i hi
    exact hposRest i (Finset.mem_of_mem_erase hi)
  have hsplitLoad :
      (∑ i ∈ S.erase h, w i) + w h = ∑ i ∈ S, w i :=
    Finset.sum_erase_add S w hh
  have hsplitTail :
      (∑ i ∈ (S.erase h).erase r, w i) + w r =
        ∑ i ∈ S.erase h, w i :=
    Finset.sum_erase_add (S.erase h) w hr
  have hrLeRest := positive_term_le_sum hposRest hr
  have hrUpper : w r < (1 / 2 : ℝ) := by
    linarith
  have hrChargeEq : harmonicCharge (w r) = (1 / 2 : ℝ) := by
    have hrUpper' : w r ≤ (1 : ℝ) / (2 : ℕ) := by
      norm_num
      exact hrUpper.le
    have hrLower' : (1 : ℝ) / ((2 : ℕ) + 1) < w r := by
      norm_num
      linarith
    simpa using
      (harmonicCharge_eq_of_band (w := w r) (r := 2) (by norm_num)
        (hposRest r hr) hrUpper' hrLower')
  have hrCharge : discountedHarmonicCharge t (w r) ≤ (1 / 2 : ℝ) := by
    rw [← hrChargeEq]
    exact discountedHarmonicCharge_le_harmonicCharge ht
  have htailLoad :
      ∑ i ∈ (S.erase h).erase r, w i < (1 / 10 : ℝ) := by
    linarith
  have htailSmall :
      ∀ i ∈ (S.erase h).erase r, w i ≤ (1 : ℝ) / (10 : ℕ) := by
    intro i hi
    have hterm := positive_term_le_sum hposTail hi
    norm_num
    linarith
  have htailCharge := discountedHarmonicCharge_sum_le_mul_weight
    ((S.erase h).erase r) w t 10 ht (by norm_num) hposTail htailSmall
  norm_num only [Nat.cast_ofNat, Nat.cast_add, Nat.cast_one] at htailCharge
  have hhCharge :=
    discountedHarmonicCharge_eq_one_minus_of_upper_range
      (t := t) hhLower hhUpper
  have hsplitChargeH :
      (∑ i ∈ S.erase h, discountedHarmonicCharge t (w i)) +
          discountedHarmonicCharge t (w h) =
        ∑ i ∈ S, discountedHarmonicCharge t (w i) :=
    Finset.sum_erase_add S (fun i => discountedHarmonicCharge t (w i)) hh
  have hsplitChargeR :
      (∑ i ∈ (S.erase h).erase r,
          discountedHarmonicCharge t (w i)) +
          discountedHarmonicCharge t (w r) =
        ∑ i ∈ S.erase h, discountedHarmonicCharge t (w i) :=
    Finset.sum_erase_add (S.erase h)
      (fun i => discountedHarmonicCharge t (w i)) hr
  linarith

/-- Case 5 of the six-case estimate: the item above one half is actually
above `3/5`, and every other item is at most one third. -/
theorem discountedHarmonicCharge_sum_very_heavy_small_remainder
    {ι : Type*} [DecidableEq ι] (S : Finset ι) (w : ι → ℝ)
    (t : ℝ) (ht : 0 ≤ t) {h : ι}
    (hpos : ∀ i ∈ S, 0 < w i)
    (hload : ∑ i ∈ S, w i ≤ 1)
    (hh : h ∈ S) (hhLower : (3 / 5 : ℝ) < w h)
    (hrestSmall : ∀ i ∈ S.erase h, w i ≤ (1 / 3 : ℝ)) :
    ∑ i ∈ S, discountedHarmonicCharge t (w i) ≤ 23 / 15 := by
  classical
  have hposRest : ∀ i ∈ S.erase h, 0 < w i := by
    intro i hi
    exact hpos i (Finset.mem_of_mem_erase hi)
  have hsplitLoad :
      (∑ i ∈ S.erase h, w i) + w h = ∑ i ∈ S, w i :=
    Finset.sum_erase_add S w hh
  have hrestLoad : ∑ i ∈ S.erase h, w i < (2 / 5 : ℝ) := by
    linarith
  have hrestCharge := discountedHarmonicCharge_sum_le_mul_weight
    (S.erase h) w t 3 ht (by norm_num) hposRest (by simpa using hrestSmall)
  norm_num only [Nat.cast_ofNat, Nat.cast_add, Nat.cast_one] at hrestCharge
  have hhLeSum := positive_term_le_sum hpos hh
  have hhUpper : w h ≤ (1 : ℝ) := hhLeSum.trans hload
  have hhChargeEq : harmonicCharge (w h) = (1 : ℝ) := by
    have hhUpper' : w h ≤ (1 : ℝ) / (1 : ℕ) := by
      norm_num
      exact hhUpper
    have hhLower' : (1 : ℝ) / ((1 : ℕ) + 1) < w h := by
      norm_num
      linarith
    simpa using
      (harmonicCharge_eq_of_band (w := w h) (r := 1) (by norm_num)
        (hpos h hh) hhUpper' hhLower')
  have hhCharge : discountedHarmonicCharge t (w h) ≤ (1 : ℝ) := by
    rw [← hhChargeEq]
    exact discountedHarmonicCharge_le_harmonicCharge ht
  have hsplitCharge :
      (∑ i ∈ S.erase h, discountedHarmonicCharge t (w i)) +
          discountedHarmonicCharge t (w h) =
        ∑ i ∈ S, discountedHarmonicCharge t (w i) :=
    Finset.sum_erase_add S (fun i => discountedHarmonicCharge t (w i)) hh
  linarith

/-- Case 6 of the six-case estimate: an item above `3/5` is accompanied by
an item above one third. -/
theorem discountedHarmonicCharge_sum_very_heavy_companion
    {ι : Type*} [DecidableEq ι] (S : Finset ι) (w : ι → ℝ)
    (t : ℝ) (ht : 0 ≤ t) {h r : ι}
    (hpos : ∀ i ∈ S, 0 < w i)
    (hload : ∑ i ∈ S, w i ≤ 1)
    (hh : h ∈ S) (hr : r ∈ S.erase h)
    (hhLower : (3 / 5 : ℝ) < w h)
    (hrLower : (1 / 3 : ℝ) < w r) :
    ∑ i ∈ S, discountedHarmonicCharge t (w i) ≤
      (707 / 450 : ℝ) - (1 / 2) * t := by
  classical
  have hposRest : ∀ i ∈ S.erase h, 0 < w i := by
    intro i hi
    exact hpos i (Finset.mem_of_mem_erase hi)
  have hposTail : ∀ i ∈ (S.erase h).erase r, 0 < w i := by
    intro i hi
    exact hposRest i (Finset.mem_of_mem_erase hi)
  have hsplitLoad :
      (∑ i ∈ S.erase h, w i) + w h = ∑ i ∈ S, w i :=
    Finset.sum_erase_add S w hh
  have hsplitTail :
      (∑ i ∈ (S.erase h).erase r, w i) + w r =
        ∑ i ∈ S.erase h, w i :=
    Finset.sum_erase_add (S.erase h) w hr
  have hrLeRest := positive_term_le_sum hposRest hr
  have hrUpper : w r < (2 / 5 : ℝ) := by
    linarith
  have hrCharge :=
    discountedHarmonicCharge_eq_half_one_minus_of_lower_range
      (t := t) hrLower hrUpper.le
  have htailLoad :
      ∑ i ∈ (S.erase h).erase r, w i < (1 / 15 : ℝ) := by
    linarith
  have htailSmall :
      ∀ i ∈ (S.erase h).erase r, w i ≤ (1 : ℝ) / (15 : ℕ) := by
    intro i hi
    have hterm := positive_term_le_sum hposTail hi
    norm_num
    linarith
  have htailCharge := discountedHarmonicCharge_sum_le_mul_weight
    ((S.erase h).erase r) w t 15 ht (by norm_num) hposTail htailSmall
  norm_num only [Nat.cast_ofNat, Nat.cast_add, Nat.cast_one] at htailCharge
  have hhLeSum := positive_term_le_sum hpos hh
  have hhUpper : w h ≤ (1 : ℝ) := hhLeSum.trans hload
  have hhChargeEq : harmonicCharge (w h) = (1 : ℝ) := by
    have hhUpper' : w h ≤ (1 : ℝ) / (1 : ℕ) := by
      norm_num
      exact hhUpper
    have hhLower' : (1 : ℝ) / ((1 : ℕ) + 1) < w h := by
      norm_num
      linarith
    simpa using
      (harmonicCharge_eq_of_band (w := w h) (r := 1) (by norm_num)
        (hpos h hh) hhUpper' hhLower')
  have hhCharge : discountedHarmonicCharge t (w h) ≤ (1 : ℝ) := by
    rw [← hhChargeEq]
    exact discountedHarmonicCharge_le_harmonicCharge ht
  have hsplitChargeH :
      (∑ i ∈ S.erase h, discountedHarmonicCharge t (w i)) +
          discountedHarmonicCharge t (w h) =
        ∑ i ∈ S, discountedHarmonicCharge t (w i) :=
    Finset.sum_erase_add S (fun i => discountedHarmonicCharge t (w i)) hh
  have hsplitChargeR :
      (∑ i ∈ (S.erase h).erase r,
          discountedHarmonicCharge t (w i)) +
          discountedHarmonicCharge t (w r) =
        ∑ i ∈ S.erase h, discountedHarmonicCharge t (w i) :=
    Finset.sum_erase_add (S.erase h)
      (fun i => discountedHarmonicCharge t (w i)) hr
  linarith

/-- The full six-case one-bin estimate.  Every finite collection of positive
weights of total load at most one has discounted charge at most the maximum
of the six manuscript bounds. -/
theorem discountedHarmonicCharge_sum_le_envelope
    {ι : Type*} [DecidableEq ι] (S : Finset ι) (w : ι → ℝ)
    (t : ℝ) (htZero : 0 ≤ t) (_htOne : t ≤ 1)
    (hpos : ∀ i ∈ S, 0 < w i)
    (hload : ∑ i ∈ S, w i ≤ 1) :
    ∑ i ∈ S, discountedHarmonicCharge t (w i) ≤
      discountedChargeEnvelope t := by
  classical
  by_cases hheavy : ∃ h ∈ S, (1 / 2 : ℝ) < w h
  · obtain ⟨h, hh, hhLower⟩ := hheavy
    by_cases hhUpper : w h ≤ (3 / 5 : ℝ)
    · by_cases hcompanion : ∃ r ∈ S.erase h, (1 / 3 : ℝ) < w r
      · obtain ⟨r, hr, hrLower⟩ := hcompanion
        by_cases hrUpper : w r ≤ (2 / 5 : ℝ)
        · exact (discountedHarmonicCharge_sum_two_discounted_items
            S w t htZero hpos hload hh hr hhLower hhUpper hrLower hrUpper).trans
            (discounted_charge_term_three_le_envelope t)
        · have hrLower' : (2 / 5 : ℝ) < w r := lt_of_not_ge hrUpper
          exact (discountedHarmonicCharge_sum_upper_heavy_large_companion
            S w t htZero hpos hload hh hr hhLower hhUpper hrLower').trans
            (discounted_charge_term_four_le_envelope t)
      · have hrestSmall :
            ∀ i ∈ S.erase h, w i ≤ (1 / 3 : ℝ) := by
          intro i hi
          by_contra hnot
          exact hcompanion ⟨i, hi, lt_of_not_ge hnot⟩
        exact (discountedHarmonicCharge_sum_upper_heavy_small_remainder
          S w t htZero hpos hload hh hhLower hhUpper hrestSmall).trans
          (discounted_charge_term_two_le_envelope t)
    · have hhLower' : (3 / 5 : ℝ) < w h := lt_of_not_ge hhUpper
      by_cases hcompanion : ∃ r ∈ S.erase h, (1 / 3 : ℝ) < w r
      · obtain ⟨r, hr, hrLower⟩ := hcompanion
        exact (discountedHarmonicCharge_sum_very_heavy_companion
          S w t htZero hpos hload hh hr hhLower' hrLower).trans
          (discounted_charge_term_six_le_envelope t)
      · have hrestSmall :
            ∀ i ∈ S.erase h, w i ≤ (1 / 3 : ℝ) := by
          intro i hi
          by_contra hnot
          exact hcompanion ⟨i, hi, lt_of_not_ge hnot⟩
        exact (discountedHarmonicCharge_sum_very_heavy_small_remainder
          S w t htZero hpos hload hh hhLower' hrestSmall).trans
          (discounted_charge_term_five_le_envelope t)
  · have hsmall : ∀ i ∈ S, w i ≤ (1 / 2 : ℝ) := by
      intro i hi
      by_contra hnot
      exact hheavy ⟨i, hi, lt_of_not_ge hnot⟩
    exact (discountedHarmonicCharge_sum_le_three_halves
      S w t htZero hpos hload hsmall).trans
      (discounted_charge_term_one_le_envelope t)

theorem harmonicSelectionFraction_nonneg :
    0 ≤ harmonicSelectionFraction :=
  harmonicSelectionFraction_pos.le

theorem harmonicSelectionFraction_le_one :
    harmonicSelectionFraction ≤ 1 :=
  harmonicSelectionFraction_lt_one.le

/-- At the selected fraction, the Sylvester-tail term is exactly `8/5`. -/
theorem harmonic_tail_discount_at_selection :
    harmonicBinPackingConstant -
        (3 / 2 : ℝ) * harmonicSelectionFraction = 8 / 5 := by
  unfold harmonicSelectionFraction
  ring

/-- The first of the six scalar terms is at most `8/5`. -/
theorem discounted_charge_term_one_le :
    (3 / 2 : ℝ) ≤ 8 / 5 := by
  norm_num

/-- The second of the six scalar terms is at most `8/5` at `t*`. -/
theorem discounted_charge_term_two_le :
    (79 / 48 : ℝ) - harmonicSelectionFraction ≤ 8 / 5 := by
  have ht := harmonicSelectionFraction_lower
  linarith

/-- The third of the six scalar terms is at most `8/5` at `t*`. -/
theorem discounted_charge_term_three_le :
    harmonicBinPackingConstant -
        (3 / 2 : ℝ) * harmonicSelectionFraction ≤ 8 / 5 := by
  rw [harmonic_tail_discount_at_selection]

/-- The fourth of the six scalar terms is at most `8/5` at `t*`. -/
theorem discounted_charge_term_four_le :
    (161 / 100 : ℝ) - harmonicSelectionFraction ≤ 8 / 5 := by
  have ht := harmonicSelectionFraction_lower
  linarith

/-- The fifth of the six scalar terms is at most `8/5`. -/
theorem discounted_charge_term_five_le :
    (23 / 15 : ℝ) ≤ 8 / 5 := by
  norm_num

/-- The sixth of the six scalar terms is at most `8/5` at `t*`. -/
theorem discounted_charge_term_six_le :
    (707 / 450 : ℝ) -
        (1 / 2 : ℝ) * harmonicSelectionFraction ≤ 8 / 5 := by
  have ht := harmonicSelectionFraction_nonneg
  linarith

/-- The maximum of all six scalar terms is at most `8/5` at `t*`. -/
theorem discountedChargeEnvelope_at_selection_le :
    discountedChargeEnvelope harmonicSelectionFraction ≤ 8 / 5 := by
  unfold discountedChargeEnvelope
  simp only [max_le_iff]
  exact ⟨discounted_charge_term_one_le,
    discounted_charge_term_two_le,
    discounted_charge_term_three_le,
    discounted_charge_term_four_le,
    discounted_charge_term_five_le,
    discounted_charge_term_six_le⟩

/-- The third scalar term witnesses the reverse inequality, so the envelope
is exactly `8/5`. -/
theorem discountedChargeEnvelope_at_selection :
    discountedChargeEnvelope harmonicSelectionFraction = 8 / 5 := by
  apply le_antisymm discountedChargeEnvelope_at_selection_le
  unfold discountedChargeEnvelope
  have hthird :
      (8 / 5 : ℝ) ≤
        harmonicBinPackingConstant -
          (3 / 2 : ℝ) * harmonicSelectionFraction := by
    rw [harmonic_tail_discount_at_selection]
  exact le_trans hthird
    (le_max_left _ (max (161 / 100 - harmonicSelectionFraction)
      (max (23 / 15) (707 / 450 - (1 / 2) * harmonicSelectionFraction)))) |>.trans
      (le_max_right _ _) |>.trans
      (le_max_right _ _)

/-- The two palette costs combine to the manuscript's coefficient
`h∞ + 2/5`. -/
theorem selected_plus_residual_coefficient_identity :
    (3 / 2 : ℝ) * harmonicSelectionFraction + 2 =
      harmonicBinPackingConstant + 2 / 5 := by
  nlinarith [harmonic_selection_coefficient_identity]

/-- The exact one-bin bound at the manuscript's selected fraction `t*`. -/
theorem discountedHarmonicCharge_sum_at_selection_le_eight_fifths
    {ι : Type*} [DecidableEq ι] (S : Finset ι) (w : ι → ℝ)
    (hpos : ∀ i ∈ S, 0 < w i)
    (hload : ∑ i ∈ S, w i ≤ 1) :
    ∑ i ∈ S,
        discountedHarmonicCharge harmonicSelectionFraction (w i) ≤
      8 / 5 := by
  have hbound := discountedHarmonicCharge_sum_le_envelope
    S w harmonicSelectionFraction harmonicSelectionFraction_nonneg
      harmonicSelectionFraction_le_one hpos hload
  rw [discountedChargeEnvelope_at_selection] at hbound
  exact hbound

/-- Finite-type form of the exact selected-fraction one-bin bound. -/
theorem discountedHarmonicCharge_sum_univ_at_selection_le_eight_fifths
    {ι : Type*} [Fintype ι] (w : ι → ℝ)
    (hpos : ∀ i, 0 < w i)
    (hload : ∑ i, w i ≤ 1) :
    ∑ i, discountedHarmonicCharge harmonicSelectionFraction (w i) ≤
      8 / 5 := by
  classical
  exact discountedHarmonicCharge_sum_at_selection_le_eight_fifths
    Finset.univ w (fun i _ => hpos i) hload

end WeightedEdgeColoring
