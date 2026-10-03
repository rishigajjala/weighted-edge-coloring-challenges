import WeightedEdgeColoring.HarmonicConstant
import Mathlib.Algebra.Order.Floor.Semifield

/-!
# Harmonic charge in one bin

This file formalizes the elementary packing lemma used by the manuscript's
harmonic upper bounds.  An item of weight `w` receives charge
`1 / floor (1 / w)`.  The main theorem says that every finite unit bin of
positive weights has total charge at most the Sylvester reciprocal constant
`harmonicBinPackingConstant`.
-/

open scoped BigOperators

namespace WeightedEdgeColoring

/-- The harmonic charge of a real weight.  For the intended range
`0 < w ≤ 1`, the denominator is a positive natural number. -/
noncomputable def harmonicCharge (w : ℝ) : ℝ :=
  (1 : ℝ) / (⌊(1 : ℝ) / w⌋₊ : ℕ)

/-- The tail of the Sylvester reciprocal series beginning with index `n`. -/
noncomputable def harmonicBinPackingTail (n : ℕ) : ℝ :=
  ∑' k : ℕ, (1 : ℝ) / sylvesterNumber (k + n)

private theorem summable_inv_sylvesterNumber_add (n : ℕ) :
    Summable (fun k : ℕ => (1 : ℝ) / sylvesterNumber (k + n)) := by
  exact (summable_nat_add_iff n).2 summable_inv_sylvesterNumber

@[simp] theorem harmonicBinPackingTail_zero :
    harmonicBinPackingTail 0 = harmonicBinPackingConstant := by
  simp [harmonicBinPackingTail, harmonicBinPackingConstant]

/-- Peeling the first term from a Sylvester tail. -/
theorem harmonicBinPackingTail_eq (n : ℕ) :
    harmonicBinPackingTail n =
      (1 : ℝ) / sylvesterNumber n + harmonicBinPackingTail (n + 1) := by
  let f : ℕ → ℝ := fun j => (1 : ℝ) / sylvesterNumber (j + n)
  have hf : Summable f := summable_inv_sylvesterNumber_add n
  have hsplit := hf.sum_add_tsum_nat_add 1
  simp only [Finset.sum_range_one, f] at hsplit
  rw [harmonicBinPackingTail, harmonicBinPackingTail]
  simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hsplit.symm

/-- Every Sylvester tail is nonnegative. -/
theorem harmonicBinPackingTail_nonneg (n : ℕ) :
    0 ≤ harmonicBinPackingTail n := by
  unfold harmonicBinPackingTail
  exact tsum_nonneg fun _ => by positivity

/-- The first two terms of a Sylvester tail are a lower bound for it. -/
theorem harmonicBinPackingTail_two_terms_le (n : ℕ) :
    (1 : ℝ) / sylvesterNumber n +
        (1 : ℝ) / sylvesterNumber (n + 1) ≤
      harmonicBinPackingTail n := by
  rw [harmonicBinPackingTail_eq n]
  have hnext : (1 : ℝ) / sylvesterNumber (n + 1) ≤
      harmonicBinPackingTail (n + 1) := by
    rw [harmonicBinPackingTail_eq (n + 1)]
    exact le_add_of_nonneg_right (harmonicBinPackingTail_nonneg (n + 1 + 1))
  simpa [add_comm] using
    (add_le_add_left hnext ((1 : ℝ) / sylvesterNumber n))

private theorem inv_weight_floor_eq_of_band
    {w : ℝ} {r : ℕ} (hr : 0 < r)
    (hw : 0 < w) (hw_upper : w ≤ (1 : ℝ) / r)
    (hw_lower : (1 : ℝ) / (r + 1) < w) :
    ⌊(1 : ℝ) / w⌋₊ = r := by
  apply (Nat.floor_eq_iff (div_nonneg zero_le_one hw.le)).2
  constructor
  · rw [le_div_iff₀ hw]
    have hrreal : (0 : ℝ) < r := by exact_mod_cast hr
    have hwr : w * (r : ℝ) ≤ 1 := (le_div_iff₀ hrreal).1 hw_upper
    nlinarith
  · have hr1real : (0 : ℝ) < (r + 1 : ℕ) := by positivity
    rw [show (r : ℝ) + 1 = ((r + 1 : ℕ) : ℝ) by norm_num]
    exact (one_div_lt hw hr1real).2 (by simpa using hw_lower)

/-- On the Sylvester band `(1/(r+1), 1/r]`, harmonic charge is exactly `1/r`. -/
theorem harmonicCharge_eq_of_band
    {w : ℝ} {r : ℕ} (hr : 0 < r)
    (hw : 0 < w) (hw_upper : w ≤ (1 : ℝ) / r)
    (hw_lower : (1 : ℝ) / (r + 1) < w) :
    harmonicCharge w = (1 : ℝ) / r := by
  unfold harmonicCharge
  rw [inv_weight_floor_eq_of_band hr hw hw_upper hw_lower]

/-- The elementary linear estimate for harmonic charge. -/
theorem harmonicCharge_le_mul_weight
    {w : ℝ} {t : ℕ} (ht : 0 < t)
    (hw : 0 < w) (hw_upper : w ≤ (1 : ℝ) / t) :
    harmonicCharge w ≤ ((t + 1 : ℕ) : ℝ) / t * w := by
  let k : ℕ := ⌊(1 : ℝ) / w⌋₊
  have htR : (0 : ℝ) < t := by exact_mod_cast ht
  have htw : (t : ℝ) ≤ (1 : ℝ) / w := by
    rw [le_div_iff₀ hw]
    have hwt : w * (t : ℝ) ≤ 1 := (le_div_iff₀ htR).1 hw_upper
    nlinarith
  have htk : t ≤ k := by
    apply (Nat.le_floor_iff (div_nonneg zero_le_one hw.le)).2
    exact htw
  have hk : 0 < k := lt_of_lt_of_le ht htk
  have hkR : (0 : ℝ) < k := by exact_mod_cast hk
  have hk1R : (0 : ℝ) < (k + 1 : ℕ) := by positivity
  have hfloorUpper : (1 : ℝ) / w < (k : ℝ) + 1 := by
    simpa [k] using (Nat.lt_floor_add_one ((1 : ℝ) / w))
  have hwLower : (1 : ℝ) / (k + 1 : ℕ) < w := by
    rw [one_div_lt hk1R hw]
    simpa using hfloorUpper
  have hcoef :
      (1 : ℝ) / k ≤ ((t + 1 : ℕ) : ℝ) / t * ((1 : ℝ) / (k + 1 : ℕ)) := by
    rw [div_mul_div_comm]
    apply (div_le_div_iff₀ hkR (mul_pos htR hk1R)).2
    norm_num
    have htkR : (t : ℝ) ≤ k := by exact_mod_cast htk
    nlinarith
  unfold harmonicCharge
  change (1 : ℝ) / k ≤ _
  exact hcoef.trans (mul_le_mul_of_nonneg_left hwLower.le (by positivity))


/-- Harmonic charge is nonnegative for every real input. -/
theorem harmonicCharge_nonneg (w : ℝ) : 0 ≤ harmonicCharge w := by
  unfold harmonicCharge
  positivity

/-- A genuine edge weight has harmonic charge at most one. -/
theorem harmonicCharge_le_one {w : ℝ} (hw : 0 < w) (hw1 : w ≤ 1) :
    harmonicCharge w ≤ 1 := by
  let k : ℕ := ⌊(1 : ℝ) / w⌋₊
  have hk : 1 ≤ k := by
    apply (Nat.le_floor_iff (div_nonneg zero_le_one hw.le)).2
    rw [le_div_iff₀ hw]
    simpa using hw1
  have hkR : (1 : ℝ) ≤ k := by exact_mod_cast hk
  unfold harmonicCharge
  change (1 : ℝ) / k ≤ 1
  exact (div_le_one (by positivity)).2 hkR

/-- A finite collection of positive weights whose load is at most the `n`th
Sylvester reciprocal has total harmonic charge at most the corresponding
Sylvester tail.  This is the induction invariant behind the one-bin lemma. -/
theorem harmonicCharge_sum_le_tail {ι : Type*} [DecidableEq ι]
    (S : Finset ι) (w : ι → ℝ) (n : ℕ)
    (hpos : ∀ i ∈ S, 0 < w i)
    (hload : ∑ i ∈ S, w i ≤ (1 : ℝ) / sylvesterNumber n) :
    ∑ i ∈ S, harmonicCharge (w i) ≤ harmonicBinPackingTail n := by
  classical
  induction S using Finset.strongInductionOn generalizing n with
  | _ S ih =>
      let r := sylvesterNumber n
      have hr : 0 < r := sylvesterNumber_pos n
      have hrR : (0 : ℝ) < r := by exact_mod_cast hr
      by_cases hlarge : ∃ i ∈ S, (1 : ℝ) / (r + 1) < w i
      · obtain ⟨i, hiS, hiLarge⟩ := hlarge
        have hwi_le_sum : w i ≤ ∑ j ∈ S, w j :=
          Finset.single_le_sum (fun j hj => (hpos j hj).le) hiS
        have hwi_upper : w i ≤ (1 : ℝ) / r :=
          hwi_le_sum.trans hload
        have hcharge : harmonicCharge (w i) = (1 : ℝ) / r :=
          harmonicCharge_eq_of_band hr (hpos i hiS) hwi_upper hiLarge
        have hsumErase :
            (∑ j ∈ S.erase i, w j) + w i = ∑ j ∈ S, w j :=
          Finset.sum_erase_add S w hiS
        have hdiff :
            (1 : ℝ) / r - 1 / (r + 1) = 1 / (r * (r + 1)) := by
          field_simp
          ring
        have hloadEraseStrict :
            ∑ j ∈ S.erase i, w j < (1 : ℝ) / (r * (r + 1)) := by
          rw [← hdiff]
          nlinarith
        have hloadErase :
            ∑ j ∈ S.erase i, w j ≤
              (1 : ℝ) / sylvesterNumber (n + 1) := by
          rw [sylvesterNumber_succ]
          simpa only [Nat.cast_mul, Nat.cast_add, Nat.cast_one] using
            hloadEraseStrict.le
        have hposErase : ∀ j ∈ S.erase i, 0 < w j := by
          intro j hj
          exact hpos j (Finset.erase_subset i S hj)
        have hrec := ih (S.erase i) (Finset.erase_ssubset hiS)
          (n + 1) hposErase hloadErase
        have hsumCharge :
            (∑ j ∈ S.erase i, harmonicCharge (w j)) +
                harmonicCharge (w i) =
              ∑ j ∈ S, harmonicCharge (w j) :=
          Finset.sum_erase_add S (fun j => harmonicCharge (w j)) hiS
        rw [← hsumCharge, hcharge, harmonicBinPackingTail_eq n]
        simpa [r, add_comm] using add_le_add_right hrec ((1 : ℝ) / r)
      · have hsmall : ∀ i ∈ S, w i ≤ (1 : ℝ) / (r + 1) := by
          intro i hi
          exact le_of_not_gt (fun h => hlarge ⟨i, hi, h⟩)
        have hterm : ∀ i ∈ S,
            harmonicCharge (w i) ≤
              (((r + 1 : ℕ) + 1 : ℕ) : ℝ) / (r + 1) * w i := by
          intro i hi
          simpa only [Nat.succ_eq_add_one, Nat.cast_add, Nat.cast_one] using
            (harmonicCharge_le_mul_weight (Nat.succ_pos r)
              (hpos i hi) (by
                simpa only [Nat.cast_succ] using hsmall i hi))
        calc
          ∑ i ∈ S, harmonicCharge (w i) ≤
              ∑ i ∈ S,
                (((r + 1 : ℕ) + 1 : ℕ) : ℝ) / (r + 1) * w i := by
            exact Finset.sum_le_sum fun i hi => hterm i hi
          _ = (((r + 1 : ℕ) + 1 : ℕ) : ℝ) / (r + 1) *
                ∑ i ∈ S, w i := by
            rw [Finset.mul_sum]
          _ ≤ (((r + 1 : ℕ) + 1 : ℕ) : ℝ) / (r + 1) *
                ((1 : ℝ) / r) := by
            exact mul_le_mul_of_nonneg_left hload (by positivity)
          _ = (1 : ℝ) / r + (1 : ℝ) / (r * (r + 1)) := by
            norm_num only [Nat.cast_add, Nat.cast_one]
            field_simp
          _ = (1 : ℝ) / sylvesterNumber n +
                (1 : ℝ) / sylvesterNumber (n + 1) := by
            simp only [r, sylvesterNumber_succ, Nat.cast_mul,
              Nat.cast_add, Nat.cast_one]
          _ ≤ harmonicBinPackingTail n := harmonicBinPackingTail_two_terms_le n

/-- Harmonic charge in one bin: every finite family of positive real weights
with total weight at most one has charge at most `h∞`. -/
theorem harmonicCharge_sum_le_harmonicBinPackingConstant
    {ι : Type*} [DecidableEq ι] (S : Finset ι) (w : ι → ℝ)
    (hpos : ∀ i ∈ S, 0 < w i)
    (hload : ∑ i ∈ S, w i ≤ 1) :
    ∑ i ∈ S, harmonicCharge (w i) ≤ harmonicBinPackingConstant := by
  have hload' : ∑ i ∈ S, w i ≤
      (1 : ℝ) / sylvesterNumber 0 := by
    simpa using hload
  simpa using harmonicCharge_sum_le_tail S w 0 hpos hload'


/-- Version of the one-bin theorem for all elements of a finite type. -/
theorem harmonicCharge_sum_univ_le_harmonicBinPackingConstant
    {ι : Type*} [Fintype ι] (w : ι → ℝ)
    (hpos : ∀ i, 0 < w i)
    (hload : ∑ i, w i ≤ 1) :
    ∑ i, harmonicCharge (w i) ≤ harmonicBinPackingConstant := by
  classical
  exact harmonicCharge_sum_le_harmonicBinPackingConstant Finset.univ w
    (fun i _ => hpos i) hload

/-- Starting the Sylvester argument at `6` removes the first two terms,
`1` and `1/2`, from the available charge. -/
theorem harmonicBinPackingTail_two :
    harmonicBinPackingTail 2 = harmonicBinPackingConstant - (3 / 2 : ℝ) := by
  have hzero := harmonicBinPackingTail_eq 0
  have hone := harmonicBinPackingTail_eq 1
  simp only [harmonicBinPackingTail_zero, sylvesterNumber_zero,
    sylvesterNumber_succ, Nat.cast_one] at hzero hone
  norm_num at hzero hone ⊢
  linarith

/-- Harmonic tail below `1/6`: positive weights of total load at most `1/6`
have total charge at most `h∞ - 3/2`. -/
theorem harmonicCharge_sum_le_tail_six
    {ι : Type*} [DecidableEq ι] (S : Finset ι) (w : ι → ℝ)
    (hpos : ∀ i ∈ S, 0 < w i)
    (hload : ∑ i ∈ S, w i ≤ (1 / 6 : ℝ)) :
    ∑ i ∈ S, harmonicCharge (w i) ≤
      harmonicBinPackingConstant - (3 / 2 : ℝ) := by
  have hload' : ∑ i ∈ S, w i ≤
      (1 : ℝ) / sylvesterNumber 2 := by
    norm_num [sylvesterNumber]
    exact hload
  rw [← harmonicBinPackingTail_two]
  exact harmonicCharge_sum_le_tail S w 2 hpos hload'

end WeightedEdgeColoring
