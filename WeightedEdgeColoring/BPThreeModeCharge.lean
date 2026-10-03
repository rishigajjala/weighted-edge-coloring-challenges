import WeightedEdgeColoring.HarmonicBinCharge

/-!
# The three-mode charge certificate

This file formalizes the exact arithmetic calculation behind the
`81 / 50` bipartite multigraph bound.  The three proposal modes have total
palette cost `7 / 30`; after the proposals are removed, every unit bin has
residual harmonic charge at most `104 / 75`.
-/

open scoped BigOperators

namespace WeightedEdgeColoring

/-- Proposal probability contributed by the first row of the table. -/
noncomputable def firstModeProposal (w : ℝ) : ℝ :=
  if 1 / 2 < w ∧ w ≤ 5 / 8 then 1 / 20
  else if 1 / 3 < w ∧ w ≤ 3 / 8 then 1 / 20 else 0

/-- Proposal probability contributed by the second row of the table. -/
noncomputable def secondModeProposal (w : ℝ) : ℝ :=
  if 1 / 2 < w ∧ w ≤ 7 / 12 then 1 / 10
  else if 1 / 3 < w ∧ w ≤ 5 / 12 then 1 / 10 else 0

/-- Proposal probability contributed by the third row of the table. -/
noncomputable def thirdModeProposal (w : ℝ) : ℝ :=
  if 1 / 2 < w ∧ w ≤ 17 / 24 then 1 / 12
  else if 1 / 4 < w ∧ w ≤ 7 / 24 then 1 / 18 else 0

/-- Total proposal probability in the three compatible modes. -/
noncomputable def threeModeProposal (w : ℝ) : ℝ :=
  firstModeProposal w + secondModeProposal w + thirdModeProposal w

/-- Harmonic charge left after the three proposal modes. -/
noncomputable def threeModeResidualCharge (w : ℝ) : ℝ :=
  harmonicCharge w * (1 - threeModeProposal w)

/-- The three palettes together use `7 / 30` times the local packing number. -/
theorem threeMode_palette_cost :
    (1 / 20 : ℝ) + 1 / 10 + 1 / 12 = 7 / 30 := by
  norm_num

theorem threeModeProposal_nonneg (w : ℝ) : 0 ≤ threeModeProposal w := by
  unfold threeModeProposal firstModeProposal secondModeProposal thirdModeProposal
  positivity

theorem threeModeProposal_le_seven_thirtieth (w : ℝ) :
    threeModeProposal w ≤ 7 / 30 := by
  have h1 : firstModeProposal w ≤ 1 / 20 := by
    unfold firstModeProposal
    split_ifs <;> norm_num
  have h2 : secondModeProposal w ≤ 1 / 10 := by
    unfold secondModeProposal
    split_ifs <;> norm_num
  have h3 : thirdModeProposal w ≤ 1 / 12 := by
    unfold thirdModeProposal
    split_ifs <;> norm_num
  unfold threeModeProposal
  linarith

private theorem residual_extra_le_heavy_one
    {w : ℝ} (hl : 1 / 2 < w) (hu : w ≤ 7 / 12) :
    threeModeResidualCharge w - (14 / 13 : ℝ) * w ≤ 89 / 390 := by
  have ha : harmonicCharge w = 1 := by
    simpa using harmonicCharge_eq_of_band (w := w) (r := 1) (by omega)
      (by linarith) (by norm_num; linarith) (by norm_num; linarith)
  rw [threeModeResidualCharge, ha]
  have hp : threeModeProposal w = 7 / 30 := by
    simp only [threeModeProposal, firstModeProposal, secondModeProposal,
      thirdModeProposal]
    rw [if_pos (by constructor <;> linarith)]
    rw [if_pos (by constructor <;> linarith)]
    rw [if_pos (by constructor <;> linarith)]
    norm_num
  rw [hp]
  linarith

private theorem residual_extra_le_heavy_two
    {w : ℝ} (hl : 7 / 12 < w) (hu : w ≤ 5 / 8) :
    threeModeResidualCharge w - (14 / 13 : ℝ) * w ≤ 31 / 130 := by
  have ha : harmonicCharge w = 1 := by
    simpa using harmonicCharge_eq_of_band (w := w) (r := 1) (by omega)
      (by linarith) (by norm_num; linarith) (by norm_num; linarith)
  rw [threeModeResidualCharge, ha]
  have hp : threeModeProposal w = 2 / 15 := by
    simp only [threeModeProposal, firstModeProposal, secondModeProposal,
      thirdModeProposal]
    rw [if_pos (by constructor <;> linarith)]
    rw [if_neg (by intro h; linarith [h.2])]
    rw [if_neg (by intro h; linarith [h.1])]
    rw [if_pos (by constructor <;> linarith)]
    norm_num
  rw [hp]
  linarith

private theorem residual_extra_le_heavy_three
    {w : ℝ} (hl : 5 / 8 < w) (hu : w ≤ 1) :
    threeModeResidualCharge w - (14 / 13 : ℝ) * w ≤ 19 / 78 := by
  have ha : harmonicCharge w = 1 := by
    simpa using harmonicCharge_eq_of_band (w := w) (r := 1) (by omega)
      (by linarith) (by norm_num; linarith) (by norm_num; linarith)
  rw [threeModeResidualCharge, ha]
  have h1 : firstModeProposal w = 0 := by
    unfold firstModeProposal
    rw [if_neg (by intro h; linarith [h.2])]
    rw [if_neg (by intro h; linarith [h.1])]
  have h2 : secondModeProposal w = 0 := by
    unfold secondModeProposal
    rw [if_neg (by intro h; linarith [h.2])]
    rw [if_neg (by intro h; linarith [h.1])]
  by_cases h17 : w ≤ 17 / 24
  · have h3 : thirdModeProposal w = 1 / 12 := by
      unfold thirdModeProposal
      rw [if_pos (by constructor <;> linarith)]
    simp [threeModeProposal, h1, h2, h3]
    linarith
  · have h3 : thirdModeProposal w = 0 := by
      unfold thirdModeProposal
      rw [if_neg (by intro h; linarith [h.2])]
      rw [if_neg (by intro h; linarith [h.1])]
    simp [threeModeProposal, h1, h2, h3]
    linarith

private theorem residual_extra_le_band_two
    {w : ℝ} (hl : 1 / 3 < w) (hu : w ≤ 1 / 2) :
    threeModeResidualCharge w - (14 / 13 : ℝ) * w ≤ 103 / 1560 := by
  have ha : harmonicCharge w = 1 / 2 := by
    convert harmonicCharge_eq_of_band (w := w) (r := 2) (by omega)
      (by linarith) hu (by norm_num; linarith) using 1 <;> norm_num
  rw [threeModeResidualCharge, ha]
  have h3 : thirdModeProposal w = 0 := by
    unfold thirdModeProposal
    rw [if_neg (by intro h; linarith [h.1])]
    rw [if_neg (by intro h; linarith [h.2])]
  by_cases h38 : w ≤ 3 / 8
  · have h1 : firstModeProposal w = 1 / 20 := by
      unfold firstModeProposal
      rw [if_neg (by intro h; linarith [h.1])]
      rw [if_pos (by constructor <;> linarith)]
    have h2 : secondModeProposal w = 1 / 10 := by
      unfold secondModeProposal
      rw [if_neg (by intro h; linarith [h.1])]
      rw [if_pos (by constructor <;> linarith)]
    simp [threeModeProposal, h1, h2, h3]
    linarith
  · by_cases h512 : w ≤ 5 / 12
    · have h1 : firstModeProposal w = 0 := by
        unfold firstModeProposal
        rw [if_neg (by intro h; linarith [h.1])]
        rw [if_neg (by intro h; linarith [h.2])]
      have h2 : secondModeProposal w = 1 / 10 := by
        unfold secondModeProposal
        rw [if_neg (by intro h; linarith [h.1])]
        rw [if_pos (by constructor <;> linarith)]
      simp [threeModeProposal, h1, h2, h3]
      linarith
    · have h1 : firstModeProposal w = 0 := by
        unfold firstModeProposal
        rw [if_neg (by intro h; linarith [h.1])]
        rw [if_neg (by intro h; linarith [h.2])]
      have h2 : secondModeProposal w = 0 := by
        unfold secondModeProposal
        rw [if_neg (by intro h; linarith [h.1])]
        rw [if_neg (by intro h; linarith [h.2])]
      simp [threeModeProposal, h1, h2, h3]
      linarith

private theorem residual_extra_le_band_three
    {w : ℝ} (hl : 1 / 4 < w) (hu : w ≤ 1 / 3) :
    threeModeResidualCharge w - (14 / 13 : ℝ) * w ≤ 16 / 351 := by
  have ha : harmonicCharge w = 1 / 3 := by
    convert harmonicCharge_eq_of_band (w := w) (r := 3) (by omega)
      (by linarith) hu (by norm_num; linarith) using 1 <;> norm_num
  rw [threeModeResidualCharge, ha]
  have h1 : firstModeProposal w = 0 := by
    unfold firstModeProposal
    rw [if_neg (by intro h; linarith [h.1])]
    rw [if_neg (by intro h; linarith [h.2])]
  have h2 : secondModeProposal w = 0 := by
    unfold secondModeProposal
    rw [if_neg (by intro h; linarith [h.1])]
    rw [if_neg (by intro h; linarith [h.2])]
  by_cases h724 : w ≤ 7 / 24
  · have h3 : thirdModeProposal w = 1 / 18 := by
      unfold thirdModeProposal
      rw [if_neg (by intro h; linarith [h.1])]
      rw [if_pos (by constructor <;> linarith)]
    simp [threeModeProposal, h1, h2, h3]
    linarith
  · have h3 : thirdModeProposal w = 0 := by
      unfold thirdModeProposal
      rw [if_neg (by intro h; linarith [h.1])]
      rw [if_neg (by intro h; linarith [h.2])]
    simp [threeModeProposal, h1, h2, h3]
    linarith

private theorem residual_extra_le_plain_band
    {w : ℝ} {r : ℕ} (hr : 3 < r)
    (hw : 0 < w) (hl : (1 : ℝ) / (r + 1) < w)
    (hu : w ≤ (1 : ℝ) / r) :
    threeModeResidualCharge w - (14 / 13 : ℝ) * w ≤
      (1 : ℝ) / r - (14 / 13 : ℝ) / (r + 1) := by
  have ha : harmonicCharge w = (1 : ℝ) / r :=
    harmonicCharge_eq_of_band (Nat.zero_lt_of_lt hr) hw hu hl
  have hquarter : w ≤ 1 / 4 := by
    have hr4 : 4 ≤ r := by omega
    have hrR : (0 : ℝ) < r := by exact_mod_cast Nat.zero_lt_of_lt hr
    have h4r : (4 : ℝ) ≤ r := by exact_mod_cast hr4
    exact hu.trans (one_div_le_one_div_of_le (by norm_num) h4r)
  have hp : threeModeProposal w = 0 := by
    have h1 : firstModeProposal w = 0 := by
      unfold firstModeProposal
      rw [if_neg (by intro h; linarith [h.1])]
      rw [if_neg (by intro h; linarith [h.1])]
    have h2 : secondModeProposal w = 0 := by
      unfold secondModeProposal
      rw [if_neg (by intro h; linarith [h.1])]
      rw [if_neg (by intro h; linarith [h.1])]
    have h3 : thirdModeProposal w = 0 := by
      unfold thirdModeProposal
      rw [if_neg (by intro h; linarith [h.1])]
      rw [if_neg (by intro h; linarith [h.1])]
    simp [threeModeProposal, h1, h2, h3]
  rw [threeModeResidualCharge, ha, hp]
  have h14 : (0 : ℝ) < 14 / 13 := by norm_num
  have hmul := mul_lt_mul_of_pos_left hl h14
  calc
    (1 : ℝ) / r * (1 - 0) - 14 / 13 * w ≤
        (1 : ℝ) / r - (14 / 13) * ((1 : ℝ) / (r + 1)) := by
          norm_num only [mul_one, sub_zero]
          exact sub_le_sub_left hmul.le ((1 : ℝ) / r)
    _ = (1 : ℝ) / r - (14 / 13 : ℝ) / (r + 1) := by ring

private theorem residual_charge_le_small
    {w : ℝ} (hw : 0 < w) (hu : w ≤ 1 / 13) :
    threeModeResidualCharge w ≤ (14 / 13 : ℝ) * w := by
  have hp0 := threeModeProposal_nonneg w
  have ha0 := harmonicCharge_nonneg w
  have hq : threeModeResidualCharge w ≤ harmonicCharge w := by
    rw [threeModeResidualCharge]
    nlinarith
  exact hq.trans (by
    simpa using harmonicCharge_le_mul_weight (w := w) (t := 13) (by omega) hw hu)

private def cell1 (w : ℝ) : Prop := 1 / 3 < w ∧ w ≤ 1 / 2
private def cell2 (w : ℝ) : Prop := 1 / 4 < w ∧ w ≤ 1 / 3
private def cell3 (w : ℝ) : Prop := 1 / 5 < w ∧ w ≤ 1 / 4
private def cell4 (w : ℝ) : Prop := 1 / 6 < w ∧ w ≤ 1 / 5
private def cell5 (w : ℝ) : Prop := 1 / 7 < w ∧ w ≤ 1 / 6
private def cell6 (w : ℝ) : Prop := 1 / 8 < w ∧ w ≤ 1 / 7
private def cell7 (w : ℝ) : Prop := 1 / 9 < w ∧ w ≤ 1 / 8
private def cell8 (w : ℝ) : Prop := 1 / 10 < w ∧ w ≤ 1 / 9
private def cell9 (w : ℝ) : Prop := 1 / 11 < w ∧ w ≤ 1 / 10
private def cell10 (w : ℝ) : Prop := 1 / 12 < w ∧ w ≤ 1 / 11
private def cell11 (w : ℝ) : Prop := 1 / 13 < w ∧ w ≤ 1 / 12

private noncomputable def nonheavyCapacity (w : ℝ) : ℕ := by
  classical
  exact if 1 / 3 < w then 120120
    else if 1 / 4 < w then 90090
    else if 1 / 5 < w then 72072
    else if 1 / 6 < w then 60060
    else if 1 / 7 < w then 51480
    else if 1 / 8 < w then 45045
    else if 1 / 9 < w then 40040
    else if 1 / 10 < w then 36036
    else if 1 / 11 < w then 32760
    else if 1 / 12 < w then 30030
    else if 1 / 13 < w then 27720 else 0

private noncomputable def nonheavyProfit (w : ℝ) : ℕ := by
  classical
  exact if 1 / 3 < w then 927927
    else if 1 / 4 < w then 640640
    else if 1 / 5 < w then 486486
    else if 1 / 6 < w then 288288
    else if 1 / 7 < w then 180180
    else if 1 / 8 < w then 115830
    else if 1 / 9 < w then 75075
    else if 1 / 10 < w then 48048
    else if 1 / 11 < w then 29484
    else if 1 / 12 < w then 16380
    else if 1 / 13 < w then 6930 else 0

set_option maxHeartbeats 1000000 in
private theorem nonheavy_cell_estimates {w : ℝ}
    (hw : 0 < w) (hu : w ≤ 1 / 2) :
    (nonheavyCapacity w : ℝ) < 360360 * w ∧
      14054040 *
          (threeModeResidualCharge w - (14 / 13 : ℝ) * w) ≤
        nonheavyProfit w := by
  classical
  by_cases h1 : 1 / 3 < w
  · have hc : cell1 w := ⟨h1, hu⟩
    have hn2 : ¬cell2 w := by intro h; linarith [h.2]
    have hn3 : ¬cell3 w := by intro h; linarith [h.2]
    have hn4 : ¬cell4 w := by intro h; linarith [h.2]
    have hn5 : ¬cell5 w := by intro h; linarith [h.2]
    have hn6 : ¬cell6 w := by intro h; linarith [h.2]
    have hn7 : ¬cell7 w := by intro h; linarith [h.2]
    have hn8 : ¬cell8 w := by intro h; linarith [h.2]
    have hn9 : ¬cell9 w := by intro h; linarith [h.2]
    have hn10 : ¬cell10 w := by intro h; linarith [h.2]
    have hn11 : ¬cell11 w := by intro h; linarith [h.2]
    have he := residual_extra_le_band_two h1 hu
    have hcap : nonheavyCapacity w = 120120 := by
      rw [nonheavyCapacity, if_pos h1]
    have hprofit : nonheavyProfit w = 927927 := by
      rw [nonheavyProfit, if_pos h1]
    rw [hcap, hprofit]
    constructor <;> norm_num at he ⊢ <;> nlinarith
  · have hu1 : w ≤ 1 / 3 := le_of_not_gt h1
    by_cases h2 : 1 / 4 < w
    · have hc : cell2 w := ⟨h2, hu1⟩
      have he := residual_extra_le_band_three h2 hu1
      have hn1 : ¬cell1 w := by intro h; exact h1 h.1
      have hn3 : ¬cell3 w := by intro h; linarith [h.2]
      have hn4 : ¬cell4 w := by intro h; linarith [h.2]
      have hn5 : ¬cell5 w := by intro h; linarith [h.2]
      have hn6 : ¬cell6 w := by intro h; linarith [h.2]
      have hn7 : ¬cell7 w := by intro h; linarith [h.2]
      have hn8 : ¬cell8 w := by intro h; linarith [h.2]
      have hn9 : ¬cell9 w := by intro h; linarith [h.2]
      have hn10 : ¬cell10 w := by intro h; linarith [h.2]
      have hn11 : ¬cell11 w := by intro h; linarith [h.2]
      rw [nonheavyCapacity, if_neg h1, if_pos h2,
        nonheavyProfit, if_neg h1, if_pos h2]
      constructor <;> norm_num at he ⊢ <;> nlinarith
    · have hu2 : w ≤ 1 / 4 := le_of_not_gt h2
      by_cases h3 : 1 / 5 < w
      · have he := residual_extra_le_plain_band (w := w) (r := 4)
            (by omega) hw (by norm_num; linarith) (by norm_num; linarith)
        rw [nonheavyCapacity, if_neg h1, if_neg h2, if_pos h3,
          nonheavyProfit, if_neg h1, if_neg h2, if_pos h3]
        constructor <;> norm_num at he ⊢ <;> nlinarith
      · have hu3 : w ≤ 1 / 5 := le_of_not_gt h3
        by_cases h4 : 1 / 6 < w
        · have he := residual_extra_le_plain_band (w := w) (r := 5)
              (by omega) hw (by norm_num; linarith) (by norm_num; linarith)
          rw [nonheavyCapacity, if_neg h1, if_neg h2, if_neg h3, if_pos h4,
            nonheavyProfit, if_neg h1, if_neg h2, if_neg h3, if_pos h4]
          constructor <;> norm_num at he ⊢ <;> nlinarith
        · have hu4 : w ≤ 1 / 6 := le_of_not_gt h4
          by_cases h5 : 1 / 7 < w
          · have he := residual_extra_le_plain_band (w := w) (r := 6)
                (by omega) hw (by norm_num; linarith) (by norm_num; linarith)
            rw [nonheavyCapacity, if_neg h1, if_neg h2, if_neg h3, if_neg h4,
              if_pos h5, nonheavyProfit, if_neg h1, if_neg h2, if_neg h3,
              if_neg h4, if_pos h5]
            constructor <;> norm_num at he ⊢ <;> nlinarith
          · have hu5 : w ≤ 1 / 7 := le_of_not_gt h5
            by_cases h6 : 1 / 8 < w
            · have he := residual_extra_le_plain_band (w := w) (r := 7)
                  (by omega) hw (by norm_num; linarith) (by norm_num; linarith)
              rw [nonheavyCapacity, if_neg h1, if_neg h2, if_neg h3, if_neg h4,
                if_neg h5, if_pos h6, nonheavyProfit, if_neg h1, if_neg h2,
                if_neg h3, if_neg h4, if_neg h5, if_pos h6]
              constructor <;> norm_num at he ⊢ <;> nlinarith
            · have hu6 : w ≤ 1 / 8 := le_of_not_gt h6
              by_cases h7 : 1 / 9 < w
              · have he := residual_extra_le_plain_band (w := w) (r := 8)
                    (by omega) hw (by norm_num; linarith) (by norm_num; linarith)
                rw [nonheavyCapacity, if_neg h1, if_neg h2, if_neg h3, if_neg h4,
                  if_neg h5, if_neg h6, if_pos h7, nonheavyProfit, if_neg h1,
                  if_neg h2, if_neg h3, if_neg h4, if_neg h5, if_neg h6, if_pos h7]
                constructor <;> norm_num at he ⊢ <;> nlinarith
              · have hu7 : w ≤ 1 / 9 := le_of_not_gt h7
                by_cases h8 : 1 / 10 < w
                · have he := residual_extra_le_plain_band (w := w) (r := 9)
                      (by omega) hw (by norm_num; linarith) (by norm_num; linarith)
                  rw [nonheavyCapacity, if_neg h1, if_neg h2, if_neg h3,
                    if_neg h4, if_neg h5, if_neg h6, if_neg h7, if_pos h8,
                    nonheavyProfit, if_neg h1, if_neg h2, if_neg h3, if_neg h4,
                    if_neg h5, if_neg h6, if_neg h7, if_pos h8]
                  constructor <;> norm_num at he ⊢ <;> nlinarith
                · have hu8 : w ≤ 1 / 10 := le_of_not_gt h8
                  by_cases h9 : 1 / 11 < w
                  · have he := residual_extra_le_plain_band (w := w) (r := 10)
                        (by omega) hw (by norm_num; linarith) (by norm_num; linarith)
                    rw [nonheavyCapacity, if_neg h1, if_neg h2, if_neg h3,
                      if_neg h4, if_neg h5, if_neg h6, if_neg h7, if_neg h8,
                      if_pos h9, nonheavyProfit, if_neg h1, if_neg h2, if_neg h3,
                      if_neg h4, if_neg h5, if_neg h6, if_neg h7, if_neg h8,
                      if_pos h9]
                    constructor <;> norm_num at he ⊢ <;> nlinarith
                  · have hu9 : w ≤ 1 / 11 := le_of_not_gt h9
                    by_cases h10 : 1 / 12 < w
                    · have he := residual_extra_le_plain_band (w := w) (r := 11)
                          (by omega) hw (by norm_num; linarith) (by norm_num; linarith)
                      rw [nonheavyCapacity, if_neg h1, if_neg h2, if_neg h3,
                        if_neg h4, if_neg h5, if_neg h6, if_neg h7, if_neg h8,
                        if_neg h9, if_pos h10, nonheavyProfit, if_neg h1, if_neg h2,
                        if_neg h3, if_neg h4, if_neg h5, if_neg h6, if_neg h7,
                        if_neg h8, if_neg h9, if_pos h10]
                      constructor <;> norm_num at he ⊢ <;> nlinarith
                    · have hu10 : w ≤ 1 / 12 := le_of_not_gt h10
                      by_cases h11 : 1 / 13 < w
                      · have he := residual_extra_le_plain_band (w := w) (r := 12)
                            (by omega) hw (by norm_num; linarith) (by norm_num; linarith)
                        rw [nonheavyCapacity, if_neg h1, if_neg h2, if_neg h3,
                          if_neg h4, if_neg h5, if_neg h6, if_neg h7, if_neg h8,
                          if_neg h9, if_neg h10, if_pos h11, nonheavyProfit,
                          if_neg h1, if_neg h2, if_neg h3, if_neg h4, if_neg h5,
                          if_neg h6, if_neg h7, if_neg h8, if_neg h9, if_neg h10,
                          if_pos h11]
                        constructor <;> norm_num at he ⊢ <;> nlinarith
                      · have hu11 : w ≤ 1 / 13 := le_of_not_gt h11
                        have he := residual_charge_le_small hw hu11
                        rw [nonheavyCapacity, if_neg h1, if_neg h2, if_neg h3,
                          if_neg h4, if_neg h5, if_neg h6, if_neg h7, if_neg h8,
                          if_neg h9, if_neg h10, if_neg h11, nonheavyProfit,
                          if_neg h1, if_neg h2, if_neg h3, if_neg h4, if_neg h5,
                          if_neg h6, if_neg h7, if_neg h8, if_neg h9, if_neg h10,
                          if_neg h11]
                        constructor <;> norm_num at he ⊢ <;> nlinarith

private theorem knapsack_none
    (n1 n2 n3 n4 n5 n6 n7 n8 n9 n10 n11 : ℕ)
    (h : 120120*n1 + 90090*n2 + 72072*n3 + 60060*n4 + 51480*n5 +
      45045*n6 + 40040*n7 + 36036*n8 + 32760*n9 + 30030*n10 +
      27720*n11 ≤ 360359) :
    5*(927927*n1 + 640640*n2 + 486486*n3 + 288288*n4 + 180180*n5 +
      115830*n6 + 75075*n7 + 48048*n8 + 29484*n9 + 16380*n10 +
      6930*n11) ≤ 21765744 := by
  have hr :
      120120*(927927*n1 + 640640*n2 + 486486*n3 + 288288*n4 +
        180180*n5 + 115830*n6 + 75075*n7 + 48048*n8 + 29484*n9 +
        16380*n10 + 6930*n11) ≤
      927927*(120120*n1 + 90090*n2 + 72072*n3 + 60060*n4 +
        51480*n5 + 45045*n6 + 40040*n7 + 36036*n8 + 32760*n9 +
        30030*n10 + 27720*n11) := by omega
  omega

set_option maxHeartbeats 800000 in
private theorem knapsack_half
    (n1 n2 n3 n4 n5 n6 n7 n8 n9 n10 n11 : ℕ)
    (h : 120120*n1 + 90090*n2 + 72072*n3 + 60060*n4 + 51480*n5 +
      45045*n6 + 40040*n7 + 36036*n8 + 32760*n9 + 30030*n10 +
      27720*n11 ≤ 180179) :
    5*(927927*n1 + 640640*n2 + 486486*n3 + 288288*n4 + 180180*n5 +
      115830*n6 + 75075*n7 + 48048*n8 + 29484*n9 + 16380*n10 +
      6930*n11) ≤ 5729724 := by
  have hn1 : n1 ≤ 1 := by omega
  have hn2 : n2 ≤ 1 := by omega
  have hn3 : n3 ≤ 2 := by omega
  have ht4 : 5*(288288*n4 + 180180*n5 + 115830*n6 + 75075*n7 +
      48048*n8 + 29484*n9 + 16380*n10 + 6930*n11) ≤
      24*(60060*n4 + 51480*n5 + 45045*n6 + 40040*n7 + 36036*n8 +
        32760*n9 + 30030*n10 + 27720*n11) := by omega
  have ht5 : 2*(180180*n5 + 115830*n6 + 75075*n7 + 48048*n8 +
      29484*n9 + 16380*n10 + 6930*n11) ≤
      7*(51480*n5 + 45045*n6 + 40040*n7 + 36036*n8 + 32760*n9 +
        30030*n10 + 27720*n11) := by omega
  have hex1 : n1 = 1 → n4 = 0 := by intro; omega
  have hex2 : n2 = 1 → n3 = 1 →
      n4+n5+n6+n7+n8+n9+n10+n11 = 0 := by intros; omega
  have hR : (120120:ℝ)*n1 + 90090*n2 + 72072*n3 + 60060*n4 +
      51480*n5 + 45045*n6 + 40040*n7 + 36036*n8 + 32760*n9 +
      30030*n10 + 27720*n11 ≤ 180179 := by exact_mod_cast h
  have ht4R : (5:ℝ)*(288288*n4 + 180180*n5 + 115830*n6 +
      75075*n7 + 48048*n8 + 29484*n9 + 16380*n10 + 6930*n11) ≤
      24*(60060*n4 + 51480*n5 + 45045*n6 + 40040*n7 + 36036*n8 +
        32760*n9 + 30030*n10 + 27720*n11) := by exact_mod_cast ht4
  have ht5R : (2:ℝ)*(180180*n5 + 115830*n6 + 75075*n7 + 48048*n8 +
      29484*n9 + 16380*n10 + 6930*n11) ≤
      7*(51480*n5 + 45045*n6 + 40040*n7 + 36036*n8 + 32760*n9 +
        30030*n10 + 27720*n11) := by exact_mod_cast ht5
  interval_cases n1 <;> interval_cases n2 <;> interval_cases n3 <;>
    simp_all <;> norm_num at hR ht4R ht5R ⊢ <;> nlinarith

set_option maxHeartbeats 800000 in
private theorem knapsack_seven_twelfths
    (n1 n2 n3 n4 n5 n6 n7 n8 n9 n10 n11 : ℕ)
    (h : 120120*n1 + 90090*n2 + 72072*n3 + 60060*n4 + 51480*n5 +
      45045*n6 + 40040*n7 + 36036*n8 + 32760*n9 + 30030*n10 +
      27720*n11 ≤ 150149) :
    5*(927927*n1 + 640640*n2 + 486486*n3 + 288288*n4 + 180180*n5 +
      115830*n6 + 75075*n7 + 48048*n8 + 29484*n9 + 16380*n10 +
      6930*n11) ≤ 5009004 := by
  have hn1 : n1 ≤ 1 := by omega
  have hn2 : n2 ≤ 1 := by omega
  have hn3 : n3 ≤ 2 := by omega
  have ht4 : 5*(288288*n4 + 180180*n5 + 115830*n6 + 75075*n7 +
      48048*n8 + 29484*n9 + 16380*n10 + 6930*n11) ≤
      24*(60060*n4 + 51480*n5 + 45045*n6 + 40040*n7 + 36036*n8 +
        32760*n9 + 30030*n10 + 27720*n11) := by omega
  have hex : n1 = 1 → n4+n5+n6+n7+n8+n9+n10 = 0 := by intro; omega
  have hR : (120120:ℝ)*n1 + 90090*n2 + 72072*n3 + 60060*n4 +
      51480*n5 + 45045*n6 + 40040*n7 + 36036*n8 + 32760*n9 +
      30030*n10 + 27720*n11 ≤ 150149 := by exact_mod_cast h
  have ht4R : (5:ℝ)*(288288*n4 + 180180*n5 + 115830*n6 +
      75075*n7 + 48048*n8 + 29484*n9 + 16380*n10 + 6930*n11) ≤
      24*(60060*n4 + 51480*n5 + 45045*n6 + 40040*n7 + 36036*n8 +
        32760*n9 + 30030*n10 + 27720*n11) := by exact_mod_cast ht4
  interval_cases n1 <;> interval_cases n2 <;> interval_cases n3 <;>
    simp_all <;> norm_num at hR ht4R ⊢ <;> nlinarith

set_option maxHeartbeats 800000 in
private theorem knapsack_five_eighths
    (n1 n2 n3 n4 n5 n6 n7 n8 n9 n10 n11 : ℕ)
    (h : 120120*n1 + 90090*n2 + 72072*n3 + 60060*n4 + 51480*n5 +
      45045*n6 + 40040*n7 + 36036*n8 + 32760*n9 + 30030*n10 +
      27720*n11 ≤ 135134) :
    5*(927927*n1 + 640640*n2 + 486486*n3 + 288288*n4 + 180180*n5 +
      115830*n6 + 75075*n7 + 48048*n8 + 29484*n9 + 16380*n10 +
      6930*n11) ≤ 4648644 := by
  have hn1 : n1 ≤ 1 := by omega
  have hn2 : n2 ≤ 1 := by omega
  have hn3 : n3 ≤ 1 := by omega
  have ht4 : 5*(288288*n4 + 180180*n5 + 115830*n6 + 75075*n7 +
      48048*n8 + 29484*n9 + 16380*n10 + 6930*n11) ≤
      24*(60060*n4 + 51480*n5 + 45045*n6 + 40040*n7 + 36036*n8 +
        32760*n9 + 30030*n10 + 27720*n11) := by omega
  have hex : n1 = 1 → n4+n5+n6+n7+n8+n9+n10+n11 = 0 := by intro; omega
  have hR : (120120:ℝ)*n1 + 90090*n2 + 72072*n3 + 60060*n4 +
      51480*n5 + 45045*n6 + 40040*n7 + 36036*n8 + 32760*n9 +
      30030*n10 + 27720*n11 ≤ 135134 := by exact_mod_cast h
  have ht4R : (5:ℝ)*(288288*n4 + 180180*n5 + 115830*n6 +
      75075*n7 + 48048*n8 + 29484*n9 + 16380*n10 + 6930*n11) ≤
      24*(60060*n4 + 51480*n5 + 45045*n6 + 40040*n7 + 36036*n8 +
        32760*n9 + 30030*n10 + 27720*n11) := by exact_mod_cast ht4
  interval_cases n1 <;> interval_cases n2 <;> interval_cases n3 <;>
    simp_all <;> norm_num at hR ht4R ⊢ <;> nlinarith

private theorem nonheavy_pair_cases (w : ℝ) :
    (nonheavyCapacity w = 0 ∧ nonheavyProfit w = 0) ∨
    (nonheavyCapacity w = 120120 ∧ nonheavyProfit w = 927927) ∨
    (nonheavyCapacity w = 90090 ∧ nonheavyProfit w = 640640) ∨
    (nonheavyCapacity w = 72072 ∧ nonheavyProfit w = 486486) ∨
    (nonheavyCapacity w = 60060 ∧ nonheavyProfit w = 288288) ∨
    (nonheavyCapacity w = 51480 ∧ nonheavyProfit w = 180180) ∨
    (nonheavyCapacity w = 45045 ∧ nonheavyProfit w = 115830) ∨
    (nonheavyCapacity w = 40040 ∧ nonheavyProfit w = 75075) ∨
    (nonheavyCapacity w = 36036 ∧ nonheavyProfit w = 48048) ∨
    (nonheavyCapacity w = 32760 ∧ nonheavyProfit w = 29484) ∨
    (nonheavyCapacity w = 30030 ∧ nonheavyProfit w = 16380) ∨
    (nonheavyCapacity w = 27720 ∧ nonheavyProfit w = 6930) := by
  classical
  by_cases h1 : 1 / 3 < w
  · rw [nonheavyCapacity, if_pos h1, nonheavyProfit, if_pos h1]
    simp
  · by_cases h2 : 1 / 4 < w
    · rw [nonheavyCapacity, if_neg h1, if_pos h2,
        nonheavyProfit, if_neg h1, if_pos h2]
      simp
    · by_cases h3 : 1 / 5 < w
      · rw [nonheavyCapacity, if_neg h1, if_neg h2, if_pos h3,
          nonheavyProfit, if_neg h1, if_neg h2, if_pos h3]
        simp
      · by_cases h4 : 1 / 6 < w
        · rw [nonheavyCapacity, if_neg h1, if_neg h2, if_neg h3, if_pos h4,
            nonheavyProfit, if_neg h1, if_neg h2, if_neg h3, if_pos h4]
          simp
        · by_cases h5 : 1 / 7 < w
          · rw [nonheavyCapacity, if_neg h1, if_neg h2, if_neg h3, if_neg h4,
              if_pos h5, nonheavyProfit, if_neg h1, if_neg h2, if_neg h3,
              if_neg h4, if_pos h5]
            simp
          · by_cases h6 : 1 / 8 < w
            · rw [nonheavyCapacity, if_neg h1, if_neg h2, if_neg h3, if_neg h4,
                if_neg h5, if_pos h6, nonheavyProfit, if_neg h1, if_neg h2,
                if_neg h3, if_neg h4, if_neg h5, if_pos h6]
              simp
            · by_cases h7 : 1 / 9 < w
              · rw [nonheavyCapacity, if_neg h1, if_neg h2, if_neg h3,
                  if_neg h4, if_neg h5, if_neg h6, if_pos h7, nonheavyProfit,
                  if_neg h1, if_neg h2, if_neg h3, if_neg h4, if_neg h5,
                  if_neg h6, if_pos h7]
                simp
              · by_cases h8 : 1 / 10 < w
                · rw [nonheavyCapacity, if_neg h1, if_neg h2, if_neg h3,
                    if_neg h4, if_neg h5, if_neg h6, if_neg h7, if_pos h8,
                    nonheavyProfit, if_neg h1, if_neg h2, if_neg h3, if_neg h4,
                    if_neg h5, if_neg h6, if_neg h7, if_pos h8]
                  simp
                · by_cases h9 : 1 / 11 < w
                  · rw [nonheavyCapacity, if_neg h1, if_neg h2, if_neg h3,
                      if_neg h4, if_neg h5, if_neg h6, if_neg h7, if_neg h8,
                      if_pos h9, nonheavyProfit, if_neg h1, if_neg h2, if_neg h3,
                      if_neg h4, if_neg h5, if_neg h6, if_neg h7, if_neg h8,
                      if_pos h9]
                    simp
                  · by_cases h10 : 1 / 12 < w
                    · rw [nonheavyCapacity, if_neg h1, if_neg h2, if_neg h3,
                        if_neg h4, if_neg h5, if_neg h6, if_neg h7, if_neg h8,
                        if_neg h9, if_pos h10, nonheavyProfit, if_neg h1, if_neg h2,
                        if_neg h3, if_neg h4, if_neg h5, if_neg h6, if_neg h7,
                        if_neg h8, if_neg h9, if_pos h10]
                      simp
                    · by_cases h11 : 1 / 13 < w
                      · rw [nonheavyCapacity, if_neg h1, if_neg h2, if_neg h3,
                          if_neg h4, if_neg h5, if_neg h6, if_neg h7, if_neg h8,
                          if_neg h9, if_neg h10, if_pos h11, nonheavyProfit,
                          if_neg h1, if_neg h2, if_neg h3, if_neg h4, if_neg h5,
                          if_neg h6, if_neg h7, if_neg h8, if_neg h9, if_neg h10,
                          if_pos h11]
                        simp
                      · rw [nonheavyCapacity, if_neg h1, if_neg h2, if_neg h3,
                          if_neg h4, if_neg h5, if_neg h6, if_neg h7, if_neg h8,
                          if_neg h9, if_neg h10, if_neg h11, nonheavyProfit,
                          if_neg h1, if_neg h2, if_neg h3, if_neg h4, if_neg h5,
                          if_neg h6, if_neg h7, if_neg h8, if_neg h9, if_neg h10,
                          if_neg h11]
                        simp

private noncomputable def capacityCount {iota : Type*} [DecidableEq iota]
    (S : Finset iota) (w : iota → ℝ) (c : ℕ) : ℕ :=
  (S.filter (fun i => nonheavyCapacity (w i) = c)).card

set_option maxHeartbeats 800000 in
private theorem nonheavy_sum_formulas {iota : Type*} [DecidableEq iota]
    (S : Finset iota) (w : iota → ℝ) :
    (∑ i ∈ S, nonheavyCapacity (w i)) =
        120120 * capacityCount S w 120120 +
        90090 * capacityCount S w 90090 +
        72072 * capacityCount S w 72072 +
        60060 * capacityCount S w 60060 +
        51480 * capacityCount S w 51480 +
        45045 * capacityCount S w 45045 +
        40040 * capacityCount S w 40040 +
        36036 * capacityCount S w 36036 +
        32760 * capacityCount S w 32760 +
        30030 * capacityCount S w 30030 +
        27720 * capacityCount S w 27720 ∧
    (∑ i ∈ S, nonheavyProfit (w i)) =
        927927 * capacityCount S w 120120 +
        640640 * capacityCount S w 90090 +
        486486 * capacityCount S w 72072 +
        288288 * capacityCount S w 60060 +
        180180 * capacityCount S w 51480 +
        115830 * capacityCount S w 45045 +
        75075 * capacityCount S w 40040 +
        48048 * capacityCount S w 36036 +
        29484 * capacityCount S w 32760 +
        16380 * capacityCount S w 30030 +
        6930 * capacityCount S w 27720 := by
  classical
  induction S using Finset.induction_on with
  | empty => simp [capacityCount]
  | @insert a S ha ih =>
      obtain h0 | h1 | h2 | h3 | h4 | h5 | h6 | h7 | h8 | h9 | h10 | h11 :=
        nonheavy_pair_cases (w a)
      all_goals
        simp only [Finset.sum_insert, ha, not_false_eq_true, ih.1, ih.2]
        simp [capacityCount, Finset.filter_insert, ha, * , Nat.mul_succ,
          Nat.add_assoc, Nat.add_comm, Nat.add_left_comm]
        try omega

private theorem nonheavy_capacity_sum_le {iota : Type*} [DecidableEq iota]
    (S : Finset iota) (w : iota → ℝ)
    (hpos : ∀ i ∈ S, 0 < w i) (hhalf : ∀ i ∈ S, w i ≤ 1 / 2)
    (B : ℕ) (hload : 360360 * (∑ i ∈ S, w i) ≤ (B + 1 : ℕ)) :
    ∑ i ∈ S, nonheavyCapacity (w i) ≤ B := by
  classical
  by_cases hS : S.Nonempty
  · have hterm : ∀ i ∈ S,
        (nonheavyCapacity (w i) : ℝ) < 360360 * w i := by
      intro i hi
      exact (nonheavy_cell_estimates (hpos i hi) (hhalf i hi)).1
    have hstrict := Finset.sum_lt_sum_of_nonempty hS hterm
    have hcast : ((∑ i ∈ S, nonheavyCapacity (w i) : ℕ) : ℝ) <
        ((B + 1 : ℕ) : ℝ) := by
      rw [Nat.cast_sum]
      calc
        ∑ i ∈ S, (nonheavyCapacity (w i) : ℝ) <
            ∑ i ∈ S, 360360 * w i := hstrict
        _ = 360360 * (∑ i ∈ S, w i) := by rw [Finset.mul_sum]
        _ ≤ (B + 1 : ℕ) := hload
    have hnat : (∑ i ∈ S, nonheavyCapacity (w i)) < B + 1 := by
      exact_mod_cast hcast
    omega
  · simpa [Finset.not_nonempty_iff_eq_empty.mp hS]

private theorem nonheavy_residual_sum_le {iota : Type*} [DecidableEq iota]
    (S : Finset iota) (w : iota → ℝ)
    (hpos : ∀ i ∈ S, 0 < w i) (hhalf : ∀ i ∈ S, w i ≤ 1 / 2)
    (T : ℕ) (hprofit : 5 * (∑ i ∈ S, nonheavyProfit (w i)) ≤ T) :
    ∑ i ∈ S, threeModeResidualCharge (w i) ≤
      (14 / 13 : ℝ) * (∑ i ∈ S, w i) + T / (5 * 14054040 : ℝ) := by
  have hterm : ∀ i ∈ S,
      14054040 * (threeModeResidualCharge (w i) - (14 / 13 : ℝ) * w i) ≤
        nonheavyProfit (w i) := by
    intro i hi
    exact (nonheavy_cell_estimates (hpos i hi) (hhalf i hi)).2
  have hsum := Finset.sum_le_sum hterm
  have hextra : 14054040 *
      (∑ i ∈ S, (threeModeResidualCharge (w i) - (14 / 13 : ℝ) * w i)) ≤
      ((∑ i ∈ S, nonheavyProfit (w i) : ℕ) : ℝ) := by
    rw [Finset.mul_sum]
    norm_cast at hsum ⊢
  have hprofitR : (5 : ℝ) *
      (∑ i ∈ S, nonheavyProfit (w i)) ≤ T := by
    exact_mod_cast hprofit
  have hdecomp :
      (∑ i ∈ S, threeModeResidualCharge (w i)) =
        (14 / 13 : ℝ) * (∑ i ∈ S, w i) +
          ∑ i ∈ S,
            (threeModeResidualCharge (w i) - (14 / 13 : ℝ) * w i) := by
    rw [Finset.sum_sub_distrib, Finset.mul_sum]
    ring
  rw [hdecomp]
  nlinarith

private theorem nonheavy_profit_none {iota : Type*} [DecidableEq iota]
    (S : Finset iota) (w : iota → ℝ)
    (hpos : ∀ i ∈ S, 0 < w i) (hhalf : ∀ i ∈ S, w i ≤ 1 / 2)
    (hload : ∑ i ∈ S, w i ≤ 1) :
    5 * (∑ i ∈ S, nonheavyProfit (w i)) ≤ 21765744 := by
  let n1 := capacityCount S w 120120
  let n2 := capacityCount S w 90090
  let n3 := capacityCount S w 72072
  let n4 := capacityCount S w 60060
  let n5 := capacityCount S w 51480
  let n6 := capacityCount S w 45045
  let n7 := capacityCount S w 40040
  let n8 := capacityCount S w 36036
  let n9 := capacityCount S w 32760
  let n10 := capacityCount S w 30030
  let n11 := capacityCount S w 27720
  have hc := nonheavy_capacity_sum_le S w hpos hhalf 360359 (by
    norm_num
    nlinarith)
  have hf := nonheavy_sum_formulas S w
  rw [hf.1] at hc
  rw [hf.2]
  exact knapsack_none n1 n2 n3 n4 n5 n6 n7 n8 n9 n10 n11 (by simpa [n1,
    n2, n3, n4, n5, n6, n7, n8, n9, n10, n11] using hc)

private theorem nonheavy_profit_half {iota : Type*} [DecidableEq iota]
    (S : Finset iota) (w : iota → ℝ)
    (hpos : ∀ i ∈ S, 0 < w i) (hhalf : ∀ i ∈ S, w i ≤ 1 / 2)
    (hload : ∑ i ∈ S, w i ≤ 1 / 2) :
    5 * (∑ i ∈ S, nonheavyProfit (w i)) ≤ 5729724 := by
  let n1 := capacityCount S w 120120; let n2 := capacityCount S w 90090
  let n3 := capacityCount S w 72072; let n4 := capacityCount S w 60060
  let n5 := capacityCount S w 51480; let n6 := capacityCount S w 45045
  let n7 := capacityCount S w 40040; let n8 := capacityCount S w 36036
  let n9 := capacityCount S w 32760; let n10 := capacityCount S w 30030
  let n11 := capacityCount S w 27720
  have hc := nonheavy_capacity_sum_le S w hpos hhalf 180179 (by
    norm_num
    nlinarith)
  have hf := nonheavy_sum_formulas S w
  rw [hf.1] at hc
  rw [hf.2]
  exact knapsack_half n1 n2 n3 n4 n5 n6 n7 n8 n9 n10 n11 (by simpa [n1,
    n2, n3, n4, n5, n6, n7, n8, n9, n10, n11] using hc)

private theorem nonheavy_profit_seven_twelfths {iota : Type*} [DecidableEq iota]
    (S : Finset iota) (w : iota → ℝ)
    (hpos : ∀ i ∈ S, 0 < w i) (hhalf : ∀ i ∈ S, w i ≤ 1 / 2)
    (hload : ∑ i ∈ S, w i ≤ 5 / 12) :
    5 * (∑ i ∈ S, nonheavyProfit (w i)) ≤ 5009004 := by
  let n1 := capacityCount S w 120120; let n2 := capacityCount S w 90090
  let n3 := capacityCount S w 72072; let n4 := capacityCount S w 60060
  let n5 := capacityCount S w 51480; let n6 := capacityCount S w 45045
  let n7 := capacityCount S w 40040; let n8 := capacityCount S w 36036
  let n9 := capacityCount S w 32760; let n10 := capacityCount S w 30030
  let n11 := capacityCount S w 27720
  have hc := nonheavy_capacity_sum_le S w hpos hhalf 150149 (by
    norm_num
    nlinarith)
  have hf := nonheavy_sum_formulas S w
  rw [hf.1] at hc
  rw [hf.2]
  exact knapsack_seven_twelfths n1 n2 n3 n4 n5 n6 n7 n8 n9 n10 n11 (by
    simpa [n1, n2, n3, n4, n5, n6, n7, n8, n9, n10, n11] using hc)

private theorem nonheavy_profit_five_eighths {iota : Type*} [DecidableEq iota]
    (S : Finset iota) (w : iota → ℝ)
    (hpos : ∀ i ∈ S, 0 < w i) (hhalf : ∀ i ∈ S, w i ≤ 1 / 2)
    (hload : ∑ i ∈ S, w i ≤ 3 / 8) :
    5 * (∑ i ∈ S, nonheavyProfit (w i)) ≤ 4648644 := by
  let n1 := capacityCount S w 120120; let n2 := capacityCount S w 90090
  let n3 := capacityCount S w 72072; let n4 := capacityCount S w 60060
  let n5 := capacityCount S w 51480; let n6 := capacityCount S w 45045
  let n7 := capacityCount S w 40040; let n8 := capacityCount S w 36036
  let n9 := capacityCount S w 32760; let n10 := capacityCount S w 30030
  let n11 := capacityCount S w 27720
  have hc := nonheavy_capacity_sum_le S w hpos hhalf 135134 (by
    norm_num
    nlinarith)
  have hf := nonheavy_sum_formulas S w
  rw [hf.1] at hc
  rw [hf.2]
  exact knapsack_five_eighths n1 n2 n3 n4 n5 n6 n7 n8 n9 n10 n11 (by
    simpa [n1, n2, n3, n4, n5, n6, n7, n8, n9, n10, n11] using hc)

/-- The displayed proposal is exactly the sum of the three table rows. -/
theorem threeModeProposal_decomposition (w : ℝ) :
    threeModeProposal w =
      firstModeProposal w + secondModeProposal w + thirdModeProposal w := rfl

/-- The residual charge is harmonic charge times the probability of receiving
none of the three positive labels. -/
theorem threeModeResidualCharge_eq (w : ℝ) :
    threeModeResidualCharge w =
      harmonicCharge w * (1 - threeModeProposal w) := rfl

/-- Exact three-choice charge calculation: every finite unit bin of positive
weights has residual harmonic charge at most `104 / 75`. -/
theorem threeModeResidualCharge_sum_le
    {iota : Type*} [DecidableEq iota] (S : Finset iota) (w : iota → ℝ)
    (hpos : ∀ i ∈ S, 0 < w i) (hload : ∑ i ∈ S, w i ≤ 1) :
    ∑ i ∈ S, threeModeResidualCharge (w i) ≤ 104 / 75 := by
  classical
  by_cases hheavy : ∃ i ∈ S, 1 / 2 < w i
  · obtain ⟨i, hiS, hi⟩ := hheavy
    let R := S.erase i
    have hposR : ∀ j ∈ R, 0 < w j := by
      intro j hj
      exact hpos j (Finset.erase_subset i S hj)
    have hsumErase : (∑ j ∈ R, w j) + w i = ∑ j ∈ S, w j := by
      exact Finset.sum_erase_add S w hiS
    have hwiSum : w i ≤ ∑ j ∈ S, w j :=
      Finset.single_le_sum (fun j hj => (hpos j hj).le) hiS
    have hwiOne : w i ≤ 1 := hwiSum.trans hload
    have hhalfR : ∀ j ∈ R, w j ≤ 1 / 2 := by
      intro j hj
      by_contra hnot
      have hjlarge : 1 / 2 < w j := lt_of_not_ge hnot
      have hjS : j ∈ S := Finset.erase_subset i S hj
      have hji : j ≠ i := (Finset.mem_erase.mp hj).1
      have hpair : ({i, j} : Finset iota) ⊆ S := by
        intro k hk
        simp only [Finset.mem_insert, Finset.mem_singleton] at hk
        rcases hk with rfl | rfl
        · exact hiS
        · exact hjS
      have hpairsum : ∑ k ∈ ({i, j} : Finset iota), w k ≤
          ∑ k ∈ S, w k := by
        apply Finset.sum_le_sum_of_subset_of_nonneg hpair
        intro k hkS hkpair
        exact (hpos k hkS).le
      have hij : i ≠ j := Ne.symm hji
      simp [hij] at hpairsum
      linarith
    have hchargeErase :
        (∑ j ∈ R, threeModeResidualCharge (w j)) +
            threeModeResidualCharge (w i) =
          ∑ j ∈ S, threeModeResidualCharge (w j) := by
      exact Finset.sum_erase_add S (fun j => threeModeResidualCharge (w j)) hiS
    by_cases hA : w i ≤ 7 / 12
    · have hloadR : ∑ j ∈ R, w j ≤ 1 / 2 := by nlinarith
      have hp := nonheavy_profit_half R w hposR hhalfR hloadR
      have hr := nonheavy_residual_sum_le R w hposR hhalfR 5729724 hp
      have hh := residual_extra_le_heavy_one hi hA
      norm_num at hr hh ⊢
      nlinarith
    · have hiB : 7 / 12 < w i := lt_of_not_ge hA
      by_cases hB : w i ≤ 5 / 8
      · have hloadR : ∑ j ∈ R, w j ≤ 5 / 12 := by nlinarith
        have hp := nonheavy_profit_seven_twelfths R w hposR hhalfR hloadR
        have hr := nonheavy_residual_sum_le R w hposR hhalfR 5009004 hp
        have hh := residual_extra_le_heavy_two hiB hB
        norm_num at hr hh ⊢
        nlinarith
      · have hiC : 5 / 8 < w i := lt_of_not_ge hB
        have hloadR : ∑ j ∈ R, w j ≤ 3 / 8 := by nlinarith
        have hp := nonheavy_profit_five_eighths R w hposR hhalfR hloadR
        have hr := nonheavy_residual_sum_le R w hposR hhalfR 4648644 hp
        have hh := residual_extra_le_heavy_three hiC hwiOne
        norm_num at hr hh ⊢
        nlinarith
  · have hhalf : ∀ i ∈ S, w i ≤ 1 / 2 := by
      intro i hi
      exact le_of_not_gt (fun h => hheavy ⟨i, hi, h⟩)
    have hp := nonheavy_profit_none S w hpos hhalf hload
    have hr := nonheavy_residual_sum_le S w hpos hhalf 21765744 hp
    norm_num at hr ⊢
    nlinarith

/-- Fintype version of the exact three-choice charge calculation. -/
theorem threeModeResidualCharge_sum_univ_le
    {iota : Type*} [Fintype iota] (w : iota → ℝ)
    (hpos : ∀ i, 0 < w i) (hload : ∑ i, w i ≤ 1) :
    ∑ i, threeModeResidualCharge (w i) ≤ 104 / 75 := by
  classical
  exact threeModeResidualCharge_sum_le Finset.univ w
    (fun i _ => hpos i) hload

end WeightedEdgeColoring
