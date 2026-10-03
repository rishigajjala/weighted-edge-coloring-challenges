import WeightedEdgeColoring.SubtwoHarmonicExcess

/-!
# The one-bin boundary potential

This proves the normal-bin and heavy-bin bounds underlying the frozen
potential row. Normal bins use a finite excess induction. The heavy
tail uses fifteen explicit reciprocal caps, each reduced to rational
arithmetic after the physical half-bin constraint is used.
-/

open scoped BigOperators

namespace WeightedEdgeColoring.SubtwoHarmonicRanks

theorem four_normal_excess {ι : Type*} [DecidableEq ι]
    (S : Finset ι) (w : ι → ℝ) (hcard : S.card ≤ 4)
    (hnonneg : ∀ i ∈ S, 0 ≤ w i)
    (hhalf : ∀ i ∈ S, w i ≤ 1 / 2) (hload : ∑ i ∈ S, w i ≤ 1) :
    (∑ i ∈ S, (harmonicCharge (w i) - w i)) ≤ 11 / 26 := by
  rw [Finset.sum_sub_distrib]
  by_cases hlarge : ∃ i ∈ S, 1 / 3 < w i
  · obtain ⟨i, hi, hwi⟩ := hlarge
    have hci := charge_excess_le (r := 2) (by decide) (hnonneg i hi) (hhalf i hi)
    have hwErase := Finset.sum_erase_add S w hi
    have hcErase := Finset.sum_erase_add S (fun i => harmonicCharge (w i) - w i) hi
    by_cases hsecond : ∃ j ∈ S.erase i, 1 / 3 < w j
    · obtain ⟨j, hj, hwj⟩ := hsecond
      have hjS := Finset.mem_of_mem_erase hj
      have hcj := charge_excess_le (r := 2) (by decide) (hnonneg j hjS) (hhalf j hjS)
      have hwErase₂ := Finset.sum_erase_add (S.erase i) w hj
      have hcErase₂ := Finset.sum_erase_add (S.erase i)
        (fun i => harmonicCharge (w i) - w i) hj
      have hcard₂ : ((S.erase i).erase j).card ≤ 2 := by
        rw [Finset.card_erase_of_mem hj, Finset.card_erase_of_mem hi]; omega
      have hrest := sum_charge_excess_le_prefix ((S.erase i).erase j) w 2 3
        (by decide) hcard₂
        (fun k hk => hnonneg k (Finset.mem_of_mem_erase (Finset.mem_of_mem_erase hk)))
        (by norm_num; linarith)
      norm_num [reciprocalPrefix] at hrest hci hcj
      dsimp only at hcErase hcErase₂
      simp only [Finset.sum_sub_distrib] at hcErase hcErase₂
      linarith
    · have hsmall : ∀ j ∈ S.erase i, w j ≤ 1 / 3 := by
        intro j hj; exact le_of_not_gt (fun h => hsecond ⟨j, hj, h⟩)
      have hrest := sum_charge_excess_le_card_cap (S.erase i) w 3 3 (by decide)
        (by rw [Finset.card_erase_of_mem hi]; omega)
        (fun j hj => hnonneg j (Finset.mem_of_mem_erase hj)) hsmall
      norm_num at hci hrest
      dsimp only at hcErase
      simp only [Finset.sum_sub_distrib] at hcErase
      linarith
  · have hsmall : ∀ i ∈ S, w i ≤ 1 / 3 := by
      intro i hi; exact le_of_not_gt (fun h => hlarge ⟨i, hi, h⟩)
    have h := sum_charge_excess_le_card_cap S w 4 3 (by decide) hcard hnonneg hsmall
    norm_num at h
    linarith

/-- In a normal bin, boundary harmonic charge is paid at rate at least
one half by the remaining physical capacity. -/
theorem normal_boundary_potential (w : Fin 4 → ℝ) (q : ℝ)
    (hnonneg : ∀ i, 0 ≤ w i) (hhalf : ∀ i, w i ≤ 1 / 2)
    (hq : 0 ≤ q) (hcapacity : (∑ i, w i) + q / 2 ≤ 1) :
    (3 / 2 : ℝ) * (∑ i, harmonicCharge (w i)) + (2 / 3 : ℝ) * q ≤ 111 / 52 := by
  have hex := four_normal_excess Finset.univ w (by simp)
    (fun i _ => hnonneg i) (fun i _ => hhalf i) (by linarith)
  rw [Finset.sum_sub_distrib] at hex
  linarith

private theorem ordered_tail_potential_of_caps
    (j k l : ℝ) (hj : 0 ≤ j) (hk : 0 ≤ k) (hl : 0 ≤ l)
    (a b c : ℕ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
    (hja : j ≤ 1 / (a : ℝ)) (hkb : k ≤ 1 / (b : ℝ)) (hlc : l ≤ 1 / (c : ℝ)) :
    (3 / 2 : ℝ) * harmonicCharge j + (5 / 2 : ℝ) *
      (harmonicCharge k + harmonicCharge l) - (j + k + l) ≤
      ((3 / 2 : ℝ) / a - 1 / ((a : ℝ) + 1)) +
      ((5 / 2 : ℝ) / b - 1 / ((b : ℝ) + 1)) +
      ((5 / 2 : ℝ) / c - 1 / ((c : ℝ) + 1)) := by
  have h₁ := scaled_charge_excess_le (α := 3 / 2) ha hj hja (by norm_num)
  have h₂ := scaled_charge_excess_le (α := 5 / 2) hb hk hkb (by norm_num)
  have h₃ := scaled_charge_excess_le (α := 5 / 2) hc hl hlc (by norm_num)
  linarith

theorem ordered_half_bin_tail_potential (j k l : ℝ)
    (hj : 0 ≤ j) (hk : 0 ≤ k) (hl : 0 ≤ l)
    (hkj : k ≤ j) (hlk : l ≤ k) (hload : j + k + l ≤ 1 / 2) :
    (3 / 2 : ℝ) * harmonicCharge j + (5 / 2 : ℝ) *
      (harmonicCharge k + harmonicCharge l) - (j + k + l) ≤ 167 / 220 := by
  have cap := ordered_tail_potential_of_caps j k l hj hk hl
  by_cases hj3 : 1 / 3 < j
  · have hja : j ≤ 1 / 2 := by linarith
    have hkb : k ≤ 1 / 6 := by linarith
    by_cases hk7 : 1 / 7 < k
    · have h := cap 2 6 42 (by decide) (by decide) (by decide) hja hkb (by norm_num; linarith)
      norm_num at h; linarith
    · by_cases hk8 : 1 / 8 < k
      · have h := cap 2 7 24 (by decide) (by decide) (by decide) hja
          (by norm_num; linarith) (by norm_num; linarith)
        norm_num at h; linarith
      · by_cases hk9 : 1 / 9 < k
        · have h := cap 2 8 18 (by decide) (by decide) (by decide) hja
            (by norm_num; linarith) (by norm_num; linarith)
          norm_num at h; linarith
        · by_cases hk10 : 1 / 10 < k
          · have h := cap 2 9 15 (by decide) (by decide) (by decide) hja
              (by norm_num; linarith) (by norm_num; linarith)
            norm_num at h; linarith
          · have h := cap 2 10 10 (by decide) (by decide) (by decide) hja
              (by norm_num; linarith) (by norm_num; linarith)
            norm_num at h; linarith
  · by_cases hj4 : 1 / 4 < j
    · have hja : j ≤ 1 / 3 := le_of_not_gt hj3
      have hkb : k ≤ 1 / 4 := by linarith
      by_cases hk5 : 1 / 5 < k
      · have h := cap 3 4 20 (by decide) (by decide) (by decide) hja hkb (by norm_num; linarith)
        norm_num at h; linarith
      · by_cases hk6 : 1 / 6 < k
        · have h := cap 3 5 12 (by decide) (by decide) (by decide) hja
            (by norm_num; linarith) (by norm_num; linarith)
          norm_num at h; linarith
        · by_cases hk7 : 1 / 7 < k
          · have h := cap 3 6 9 (by decide) (by decide) (by decide) hja
              (by norm_num; linarith) (by norm_num; linarith)
            norm_num at h; linarith
          · have h := cap 3 7 7 (by decide) (by decide) (by decide) hja
              (by norm_num; linarith) (by norm_num; linarith)
            norm_num at h; linarith
    · by_cases hj5 : 1 / 5 < j
      · have hja : j ≤ 1 / 4 := le_of_not_gt hj4
        by_cases hk5 : 1 / 5 < k
        · have h := cap 4 4 10 (by decide) (by decide) (by decide) hja
            (hkj.trans hja) (by norm_num; linarith)
          norm_num at h; linarith
        · by_cases hk6 : 1 / 6 < k
          · have h := cap 4 5 7 (by decide) (by decide) (by decide) hja
              (by norm_num; linarith) (by norm_num; linarith)
            norm_num at h; linarith
          · have h := cap 4 6 6 (by decide) (by decide) (by decide) hja
              (by norm_num; linarith) (by norm_num; linarith)
            norm_num at h; linarith
      · by_cases hj6 : 1 / 6 < j
        · have hja : j ≤ 1 / 5 := le_of_not_gt hj5
          by_cases hk6 : 1 / 6 < k
          · have h := cap 5 5 6 (by decide) (by decide) (by decide) hja
              (hkj.trans hja) (by norm_num; linarith)
            norm_num at h; linarith
          · have h := cap 5 6 6 (by decide) (by decide) (by decide) hja
              (by norm_num; linarith) (by norm_num; linarith)
            norm_num at h; linarith
        · have hja : j ≤ 1 / 6 := le_of_not_gt hj6
          have h := cap 6 6 6 (by decide) (by decide) (by decide) hja
            (hkj.trans hja) (hlk.trans (hkj.trans hja))
          norm_num at h; linarith

/-- Heavy-bin potential, with the largest of the three smaller projections
distinguished. Boundary harmonic charge is paid by `2q/3` physical load. -/
theorem heavy_boundary_potential (heavy second small₁ small₂ q : ℝ)
    (hh : 1 / 2 < heavy) (hs : 0 ≤ second)
    (h₁ : 0 ≤ small₁) (h₂ : 0 ≤ small₂)
    (hs₁ : small₁ ≤ second) (hs₂ : small₂ ≤ second) (hq : 0 ≤ q)
    (hcapacity : heavy + second + small₁ + small₂ + (2 / 3 : ℝ) * q ≤ 1) :
    (harmonicCharge small₁ + harmonicCharge small₂) +
      (3 / 2 : ℝ) * (harmonicCharge heavy + harmonicCharge second +
        harmonicCharge small₁ + harmonicCharge small₂) + (2 / 3 : ℝ) * q ≤ 607 / 220 := by
  have hheavy : harmonicCharge heavy = 1 := by
    have h := harmonicCharge_eq_of_band (r := 1) (by decide)
      (by linarith : 0 < heavy) (by norm_num; linarith) (by norm_num; exact hh)
    simpa using h
  have htail : (3 / 2 : ℝ) * harmonicCharge second + (5 / 2 : ℝ) *
      (harmonicCharge small₁ + harmonicCharge small₂) - (second + small₁ + small₂) ≤ 167 / 220 := by
    rcases le_total small₂ small₁ with h | h
    · exact ordered_half_bin_tail_potential second small₁ small₂ hs h₁ h₂ hs₁ h (by linarith)
    · have ht := ordered_half_bin_tail_potential second small₂ small₁ hs h₂ h₁ hs₂ h (by linarith)
      linarith
  rw [hheavy]
  linarith

end WeightedEdgeColoring.SubtwoHarmonicRanks
