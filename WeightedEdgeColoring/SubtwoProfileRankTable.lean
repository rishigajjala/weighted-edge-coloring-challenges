import WeightedEdgeColoring.SubtwoHarmonicRanks

/-!
# The complete normal and heavy projection rank tables

All bounds in this file follow from the physical loads of at most four
projections in a unit bin.  In particular, the full-star averaged row no
longer requires the harmonic rank constants as extra assumptions.
-/

open scoped BigOperators

namespace WeightedEdgeColoring.SubtwoHarmonicRanks

theorem sum_charge_le_card_cap {ι : Type*} [DecidableEq ι]
    (S : Finset ι) (w : ι → ℝ) (k r : ℕ)
    (hr : 0 < r) (hcard : S.card ≤ k)
    (hnonneg : ∀ i ∈ S, 0 ≤ w i) (hcap : ∀ i ∈ S, w i ≤ 1 / (r : ℝ)) :
    ∑ i ∈ S, harmonicCharge (w i) ≤ (k : ℝ) / r := by
  calc
    _ ≤ ∑ _i ∈ S, (1 : ℝ) / r :=
      Finset.sum_le_sum fun i hi => charge_le_inv hr (hnonneg i hi) (hcap i hi)
    _ = (S.card : ℝ) / r := by simp [div_eq_mul_inv]
    _ ≤ _ := div_le_div_of_nonneg_right (by exact_mod_cast hcard) (by positivity)

theorem three_normal_charge {ι : Type*} [DecidableEq ι]
    (S : Finset ι) (w : ι → ℝ) (hcard : S.card ≤ 3)
    (hnonneg : ∀ i ∈ S, 0 ≤ w i)
    (hhalf : ∀ i ∈ S, w i ≤ 1 / 2) (hload : ∑ i ∈ S, w i ≤ 1) :
    ∑ i ∈ S, harmonicCharge (w i) ≤ 4 / 3 := by
  by_cases hc : S.card ≤ 2
  · have h := sum_charge_le_card_cap S w 2 2 (by decide) hc hnonneg hhalf
    norm_num at h; linarith
  · have hc3 : S.card = 3 := by omega
    have hsmall : ∃ i ∈ S, w i ≤ 1 / 3 := by
      by_contra hn
      have hlarge : ∀ i ∈ S, 1 / 3 < w i := by
        intro i hi; exact lt_of_not_ge (fun h => hn ⟨i, hi, h⟩)
      obtain ⟨i, hi⟩ := Finset.card_pos.mp (show 0 < S.card by omega)
      have hsum : (∑ _j ∈ S, (1 / 3 : ℝ)) < ∑ j ∈ S, w j :=
        Finset.sum_lt_sum (fun j hj => (hlarge j hj).le) ⟨i, hi, hlarge i hi⟩
      norm_num [hc3] at hsum
      linarith
    obtain ⟨i, hi, hwi⟩ := hsmall
    have hci := charge_le_inv (r := 3) (by decide) (hnonneg i hi) hwi
    have hrest := sum_charge_le_card_cap (S.erase i) w 2 2 (by decide)
      (by rw [Finset.card_erase_of_mem hi, hc3])
      (fun j hj => hnonneg j (Finset.mem_of_mem_erase hj))
      (fun j hj => hhalf j (Finset.mem_of_mem_erase hj))
    have hsum := Finset.sum_erase_add S (fun j => harmonicCharge (w j)) hi
    norm_num at hci hrest
    linarith

noncomputable def normalRank : ℕ → ℝ
  | 0 => 0
  | 1 => 1 / 2
  | 2 => 1
  | 3 => 4 / 3
  | _ => 17 / 12

/-- Every subset rank used for a normal four-projection bin. -/
theorem normal_subset_rank {ι : Type*} [DecidableEq ι]
    (S : Finset ι) (w : ι → ℝ) (hcard : S.card ≤ 4)
    (hnonneg : ∀ i ∈ S, 0 ≤ w i)
    (hhalf : ∀ i ∈ S, w i ≤ 1 / 2) (hload : ∑ i ∈ S, w i ≤ 1) :
    ∑ i ∈ S, harmonicCharge (w i) ≤ normalRank S.card := by
  interval_cases hc : S.card
  · have hS : S = ∅ := Finset.card_eq_zero.mp hc
    subst S; simp [normalRank]
  · simpa [hc, normalRank] using
      sum_charge_le_card_cap S w 1 2 (by decide) (by omega) hnonneg hhalf
  · simpa [hc, normalRank] using
      sum_charge_le_card_cap S w 2 2 (by decide) (by omega) hnonneg hhalf
  · simpa [hc, normalRank] using three_normal_charge S w (by omega) hnonneg hhalf hload
  · simpa [hc, normalRank] using four_normal_charge S w (by omega) hnonneg hhalf hload

theorem pair_charge_half (x y : ℝ) (hx : 0 ≤ x) (hy : 0 ≤ y)
    (hload : x + y ≤ 1 / 2) : harmonicCharge x + harmonicCharge y ≤ 2 / 3 := by
  have h := two_charge_half (Finset.univ : Finset (Fin 2)) ![x, y]
    (by simp) (by intro i hi; fin_cases i <;> simp [hx, hy])
    (by simpa [Fin.sum_univ_succ] using hload)
  simpa [Fin.sum_univ_succ] using h

theorem triple_charge_half (x y z : ℝ) (hx : 0 ≤ x) (hy : 0 ≤ y) (hz : 0 ≤ z)
    (hload : x + y + z ≤ 1 / 2) :
    harmonicCharge x + harmonicCharge y + harmonicCharge z ≤ 29 / 42 := by
  have h := three_charge_half (Finset.univ : Finset (Fin 3)) ![x, y, z]
    (by simp) (by intro i hi; fin_cases i <;> simp [hx, hy, hz])
    (by simpa [Fin.sum_univ_succ, add_assoc] using hload)
  simpa [Fin.sum_univ_succ, add_assoc] using h

/-- The fifteen nonempty subset bounds in an `H(i,j)` bin. The first
coordinate is heavy; the second is the largest remaining load. -/
structure HeavyRanks (a b c d : ℝ) : Prop where
  heavy_eq : a = 1
  second_le : b ≤ 1 / 2
  small₁_le : c ≤ 1 / 4
  small₂_le : d ≤ 1 / 4
  heavy_second : a + b ≤ 3 / 2
  heavy_small₁ : a + c ≤ 5 / 4
  heavy_small₂ : a + d ≤ 5 / 4
  second_small₁ : b + c ≤ 2 / 3
  second_small₂ : b + d ≤ 2 / 3
  small_pair : c + d ≤ 11 / 30
  heavy_second_small₁ : a + b + c ≤ 5 / 3
  heavy_second_small₂ : a + b + d ≤ 5 / 3
  heavy_small_pair : a + c + d ≤ 41 / 30
  tail : b + c + d ≤ 29 / 42
  full : a + b + c + d ≤ 71 / 42

theorem heavy_subset_ranks (heavy second small₁ small₂ : ℝ)
    (hheavy : 1 / 2 < heavy) (hsecond : 0 ≤ second)
    (hsmall₁ : 0 ≤ small₁) (hsmall₂ : 0 ≤ small₂)
    (hsecond₁ : small₁ ≤ second) (hsecond₂ : small₂ ≤ second)
    (hload : heavy + second + small₁ + small₂ ≤ 1) :
    HeavyRanks (harmonicCharge heavy) (harmonicCharge second)
      (harmonicCharge small₁) (harmonicCharge small₂) := by
  have ha : harmonicCharge heavy = 1 := by
    have h := harmonicCharge_eq_of_band (r := 1) (by decide)
      (by linarith : 0 < heavy) (by norm_num; linarith)
      (by norm_num; exact hheavy)
    simpa using h
  have hb := charge_le_inv (r := 2) (by decide) hsecond (by norm_num; linarith)
  obtain ⟨_, hsmall₁₄, hsmall₂₄⟩ := SubtwoBinProfileRows.heavy_bin_smaller_loads
    heavy second small₁ small₂ hheavy hsmall₁ hsmall₂ hsecond₁ hsecond₂ hload
  have hc := charge_le_inv (r := 4) (by decide) hsmall₁ hsmall₁₄.le
  have hd := charge_le_inv (r := 4) (by decide) hsmall₂ hsmall₂₄.le
  have hbc := pair_charge_half second small₁ hsecond hsmall₁ (by linarith)
  have hbd := pair_charge_half second small₂ hsecond hsmall₂ (by linarith)
  have hcd := heavy_bin_small_pair_charge heavy second small₁ small₂
    hheavy hsmall₁ hsmall₂ hsecond₁ hsecond₂ hload
  have hbcd := triple_charge_half second small₁ small₂ hsecond hsmall₁ hsmall₂
    (by linarith)
  norm_num at hb hc hd
  constructor <;> linarith

/-- The generator's averaged full-star rank row, now from actual loads.
Its only cost premise is domination by the projected harmonic charges. -/
theorem full_star_rank_row_of_loads {B : Type*} [Fintype B]
    (mass : B → ℝ) (w : B → Fin 4 → ℝ) (t : Fin 4 → ℝ)
    (hmass : ∀ b, 0 ≤ mass b) (htotal : (∑ b, mass b) ≤ 1)
    (hnonneg : ∀ b i, 0 ≤ w b i) (hload : ∀ b, ∑ i, w b i ≤ 1)
    (ht : ∀ i, t i ≤ ∑ b, mass b * harmonicCharge (w b i)) :
    (∑ i, t i) ≤ (17 / 12 : ℝ) + (23 / 84 : ℝ) *
      ∑ b, if (∃ i, 1 / 2 < w b i) then mass b else 0 := by
  classical
  apply SubtwoBinProfileRows.full_star_rank_row mass (fun b => ∃ i, 1 / 2 < w b i)
    (fun b i => harmonicCharge (w b i)) t hmass htotal ?_ ht
  intro b
  split_ifs with hb
  · exact four_charge_unit Finset.univ (w b) (by simp) (fun i _ => hnonneg b i) (hload b)
  · apply four_normal_charge Finset.univ (w b) (by simp) (fun i _ => hnonneg b i) ?_ (hload b)
    intro i hi
    exact le_of_not_gt (fun h => hb ⟨i, h⟩)

end WeightedEdgeColoring.SubtwoHarmonicRanks
