import WeightedEdgeColoring.SubtwoBinProfileRows

/-!
# Finite harmonic ranks for projected bins

The number of projections improves the infinite harmonic bound.  The
recurrence below works from every positive integer denominator, not just
the Sylvester sequence beginning at one.  Zero projections are allowed.
-/

open scoped BigOperators

namespace WeightedEdgeColoring.SubtwoHarmonicRanks

open SubtwoBinProfileRows

noncomputable def reciprocalPrefix (r : ℕ) : ℕ → ℝ
  | 0 => 0
  | k + 1 => 1 / (r : ℝ) + reciprocalPrefix (r * (r + 1)) k

theorem reciprocalPrefix_nonneg (r k : ℕ) : 0 ≤ reciprocalPrefix r k := by
  induction k generalizing r with
  | zero => simp [reciprocalPrefix]
  | succ k ih => exact add_nonneg (by positivity) (ih _)

theorem two_terms_le_reciprocalPrefix (r k : ℕ) :
    1 / (r : ℝ) + 1 / ((r * (r + 1) : ℕ) : ℝ) ≤
      reciprocalPrefix r (k + 2) := by
  simp only [reciprocalPrefix]
  have h := reciprocalPrefix_nonneg ((r * (r + 1)) * ((r * (r + 1)) + 1)) k
  linarith

@[simp] theorem harmonicCharge_zero : harmonicCharge 0 = 0 := by
  simp [harmonicCharge]

theorem charge_le_inv {w : ℝ} {r : ℕ}
    (hr : 0 < r) (hw : 0 ≤ w) (hwr : w ≤ 1 / (r : ℝ)) :
    harmonicCharge w ≤ 1 / (r : ℝ) := by
  rcases eq_or_lt_of_le hw with h | h
  · subst w; simp
  · exact harmonicCharge_le_inv_of_le hr h hwr

theorem charge_le_linear {w : ℝ} {r : ℕ}
    (hr : 0 < r) (hw : 0 ≤ w) (hwr : w ≤ 1 / (r : ℝ)) :
    harmonicCharge w ≤ ((r + 1 : ℕ) : ℝ) / r * w := by
  rcases eq_or_lt_of_le hw with h | h
  · subst w; simp
  · exact harmonicCharge_le_mul_weight hr h hwr

/-- At most `k` nonnegative projections with total load at most `1/r`
have charge at most the first `k` reciprocal terms starting at `r`. -/
theorem sum_charge_le_reciprocalPrefix {ι : Type*} [DecidableEq ι]
    (S : Finset ι) (w : ι → ℝ) (k r : ℕ)
    (hr : 0 < r) (hcard : S.card ≤ k)
    (hnonneg : ∀ i ∈ S, 0 ≤ w i)
    (hload : ∑ i ∈ S, w i ≤ 1 / (r : ℝ)) :
    ∑ i ∈ S, harmonicCharge (w i) ≤ reciprocalPrefix r k := by
  induction k generalizing S r with
  | zero =>
      have hS : S = ∅ := Finset.card_eq_zero.mp (by omega)
      subst S; simp [reciprocalPrefix]
  | succ k ih =>
      have hrR : (0 : ℝ) < r := by exact_mod_cast hr
      cases k with
      | zero =>
          calc
            ∑ i ∈ S, harmonicCharge (w i) ≤ ∑ _i ∈ S, 1 / (r : ℝ) := by
              apply Finset.sum_le_sum
              intro i hi
              exact charge_le_inv hr (hnonneg i hi)
                ((Finset.single_le_sum hnonneg hi).trans hload)
            _ ≤ 1 / (r : ℝ) := by
              simp only [Finset.sum_const, nsmul_eq_mul]
              have hc : (S.card : ℝ) ≤ 1 := by exact_mod_cast hcard
              nlinarith [show 0 ≤ 1 / (r : ℝ) by positivity]
            _ = reciprocalPrefix r 1 := by simp [reciprocalPrefix]
      | succ k =>
          by_cases hlarge : ∃ i ∈ S, 1 / ((r : ℝ) + 1) < w i
          · obtain ⟨i, hi, hlarge⟩ := hlarge
            have hwi : 0 < w i := lt_trans (by positivity) hlarge
            have hcharge : harmonicCharge (w i) = 1 / (r : ℝ) :=
              harmonicCharge_eq_of_band hr hwi
                ((Finset.single_le_sum hnonneg hi).trans hload) hlarge
            have heq := Finset.sum_erase_add S w hi
            have hdiff : 1 / (r : ℝ) - 1 / ((r : ℝ) + 1) =
                1 / ((r : ℝ) * ((r : ℝ) + 1)) := by
              field_simp
              ring
            have herase : ∑ j ∈ S.erase i, w j ≤
                1 / ((r * (r + 1) : ℕ) : ℝ) := by
              push_cast
              rw [← hdiff]
              linarith
            have hc : (S.erase i).card ≤ k + 1 := by
              rw [Finset.card_erase_of_mem hi]; omega
            have hrec := ih (S.erase i) (r * (r + 1)) (by positivity) hc
              (fun j hj => hnonneg j (Finset.mem_of_mem_erase hj)) herase
            have hsum := Finset.sum_erase_add S (fun j => harmonicCharge (w j)) hi
            rw [reciprocalPrefix]
            linarith
          · have hsmall : ∀ i ∈ S, w i ≤ 1 / ((r : ℝ) + 1) := by
              intro i hi; exact le_of_not_gt (fun h => hlarge ⟨i, hi, h⟩)
            have hsum : ∑ i ∈ S, harmonicCharge (w i) ≤
                (((r + 1 : ℕ) + 1 : ℕ) : ℝ) / (r + 1) * ∑ i ∈ S, w i := by
              rw [Finset.mul_sum]
              apply Finset.sum_le_sum
              intro i hi
              simpa only [Nat.succ_eq_add_one, Nat.cast_add, Nat.cast_one] using
                charge_le_linear (Nat.succ_pos r) (hnonneg i hi)
                  (by simpa using hsmall i hi)
            have hcoef : (((r + 1 : ℕ) + 1 : ℕ) : ℝ) / (r + 1) *
                (1 / (r : ℝ)) =
                1 / (r : ℝ) + 1 / ((r * (r + 1) : ℕ) : ℝ) := by
              push_cast
              field_simp
            calc
              _ ≤ (((r + 1 : ℕ) + 1 : ℕ) : ℝ) / (r + 1) * ∑ i ∈ S, w i := hsum
              _ ≤ (((r + 1 : ℕ) + 1 : ℕ) : ℝ) / (r + 1) * (1 / (r : ℝ)) :=
                mul_le_mul_of_nonneg_left hload (by positivity)
              _ = _ := hcoef
              _ ≤ _ := two_terms_le_reciprocalPrefix r k

/-- Two projections below load one half have total charge at most `2/3`. -/
theorem two_charge_half {ι : Type*} [DecidableEq ι]
    (S : Finset ι) (w : ι → ℝ) (hcard : S.card ≤ 2)
    (hnonneg : ∀ i ∈ S, 0 ≤ w i) (hload : ∑ i ∈ S, w i ≤ 1 / 2) :
    ∑ i ∈ S, harmonicCharge (w i) ≤ 2 / 3 := by
  have h := sum_charge_le_reciprocalPrefix S w 2 2 (by decide) hcard hnonneg hload
  norm_num [reciprocalPrefix] at h ⊢
  exact h

/-- Three projections below load one half have total charge at most `29/42`. -/
theorem three_charge_half {ι : Type*} [DecidableEq ι]
    (S : Finset ι) (w : ι → ℝ) (hcard : S.card ≤ 3)
    (hnonneg : ∀ i ∈ S, 0 ≤ w i) (hload : ∑ i ∈ S, w i ≤ 1 / 2) :
    ∑ i ∈ S, harmonicCharge (w i) ≤ 29 / 42 := by
  have h := sum_charge_le_reciprocalPrefix S w 3 2 (by decide) hcard hnonneg hload
  norm_num [reciprocalPrefix] at h ⊢
  exact h

/-- Four projections in a unit bin have total charge at most `71/42`. -/
theorem four_charge_unit {ι : Type*} [DecidableEq ι]
    (S : Finset ι) (w : ι → ℝ) (hcard : S.card ≤ 4)
    (hnonneg : ∀ i ∈ S, 0 ≤ w i) (hload : ∑ i ∈ S, w i ≤ 1) :
    ∑ i ∈ S, harmonicCharge (w i) ≤ 71 / 42 := by
  have h := sum_charge_le_reciprocalPrefix S w 4 1 (by decide) hcard hnonneg
    (by simpa using hload)
  norm_num [reciprocalPrefix] at h ⊢
  exact h

/-- Four projections of load at most one half have the sharper rank
`17/12`. The proof needs only two threshold choices. -/
theorem four_normal_charge {ι : Type*} [DecidableEq ι]
    (S : Finset ι) (w : ι → ℝ) (hcard : S.card ≤ 4)
    (hnonneg : ∀ i ∈ S, 0 ≤ w i)
    (hhalf : ∀ i ∈ S, w i ≤ 1 / 2) (hload : ∑ i ∈ S, w i ≤ 1) :
    ∑ i ∈ S, harmonicCharge (w i) ≤ 17 / 12 := by
  by_cases hlarge : ∃ i ∈ S, 1 / 3 < w i
  · obtain ⟨i, hi, hwi⟩ := hlarge
    have hci : harmonicCharge (w i) ≤ 1 / 2 :=
      charge_le_inv (r := 2) (by decide) (hnonneg i hi) (hhalf i hi)
    have hwErase := Finset.sum_erase_add S w hi
    have hcErase := Finset.sum_erase_add S (fun i => harmonicCharge (w i)) hi
    by_cases hsecond : ∃ j ∈ S.erase i, 1 / 3 < w j
    · obtain ⟨j, hj, hwj⟩ := hsecond
      have hjS := Finset.mem_of_mem_erase hj
      have hcj : harmonicCharge (w j) ≤ 1 / 2 :=
        charge_le_inv (r := 2) (by decide) (hnonneg j hjS) (hhalf j hjS)
      have hwErase₂ := Finset.sum_erase_add (S.erase i) w hj
      have hcErase₂ := Finset.sum_erase_add (S.erase i)
        (fun i => harmonicCharge (w i)) hj
      have hcard₂ : ((S.erase i).erase j).card ≤ 2 := by
        rw [Finset.card_erase_of_mem hj, Finset.card_erase_of_mem hi]; omega
      have hrest := sum_charge_le_reciprocalPrefix ((S.erase i).erase j) w 2 3
        (by decide) hcard₂
        (fun k hk => hnonneg k (Finset.mem_of_mem_erase (Finset.mem_of_mem_erase hk)))
        (by norm_num; linarith)
      norm_num [reciprocalPrefix] at hrest
      linarith
    · have hsmall : ∀ j ∈ S.erase i, w j ≤ 1 / 3 := by
        intro j hj; exact le_of_not_gt (fun h => hsecond ⟨j, hj, h⟩)
      have hcSmall : ∑ j ∈ S.erase i, harmonicCharge (w j) ≤
          (4 / 3 : ℝ) * ∑ j ∈ S.erase i, w j := by
        rw [Finset.mul_sum]
        apply Finset.sum_le_sum
        intro j hj
        exact charge_le_linear (r := 3) (by decide)
          (hnonneg j (Finset.mem_of_mem_erase hj)) (hsmall j hj)
      linarith
  · have hsmall : ∀ i ∈ S, w i ≤ 1 / 3 := by
      intro i hi; exact le_of_not_gt (fun h => hlarge ⟨i, hi, h⟩)
    have hsum : ∑ i ∈ S, harmonicCharge (w i) ≤ (4 / 3 : ℝ) * ∑ i ∈ S, w i := by
      rw [Finset.mul_sum]
      exact Finset.sum_le_sum fun i hi =>
        charge_le_linear (r := 3) (by decide) (hnonneg i hi) (hsmall i hi)
    linarith

/-- The two smaller of three projections with total load below one half
have charge at most `11/30`. -/
theorem ordered_small_pair_charge (u v : ℝ)
    (hv : 0 ≤ v) (hvu : v ≤ u) (hload : 2 * u + v ≤ 1 / 2) :
    harmonicCharge u + harmonicCharge v ≤ 11 / 30 := by
  have hu : 0 ≤ u := hv.trans hvu
  have hu4 : u ≤ 1 / 4 := by linarith
  by_cases hu6 : u ≤ 1 / 6
  · have hcu := charge_le_inv (r := 6) (by decide) hu hu6
    have hcv := charge_le_inv (r := 6) (by decide) hv (hvu.trans hu6)
    norm_num at hcu hcv
    linarith
  · by_cases hu5 : u ≤ 1 / 5
    · have hcu := charge_le_inv (r := 5) (by decide) hu hu5
      have hcv := charge_le_inv (r := 6) (by decide) hv (by norm_num; linarith)
      norm_num at hcu hcv
      linarith
    · have hcu := charge_le_inv (r := 4) (by decide) hu hu4
      have hcv := charge_le_inv (r := 10) (by decide) hv (by norm_num; linarith)
      norm_num at hcu hcv
      linarith

theorem heavy_bin_small_pair_charge (heavy second small₁ small₂ : ℝ)
    (hheavy : 1 / 2 < heavy)
    (hsmall₁ : 0 ≤ small₁) (hsmall₂ : 0 ≤ small₂)
    (hsecond₁ : small₁ ≤ second) (hsecond₂ : small₂ ≤ second)
    (hload : heavy + second + small₁ + small₂ ≤ 1) :
    harmonicCharge small₁ + harmonicCharge small₂ ≤ 11 / 30 := by
  rcases le_total small₁ small₂ with h | h
  · have hc := ordered_small_pair_charge small₂ small₁ hsmall₁ h (by linarith)
    linarith
  · exact ordered_small_pair_charge small₁ small₂ hsmall₂ h (by linarith)

end WeightedEdgeColoring.SubtwoHarmonicRanks
