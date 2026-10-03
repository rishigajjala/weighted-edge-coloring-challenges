import WeightedEdgeColoring.SubtwoProfileRankTable

/-!
# The directed cross-cost row from actual local bin loads

The selected sublaw may be any collection of bins heavy in coordinate
zero.  Its two last projections compete with coordinate one for the
half-bin harmonic rank.  No agreement between endpoint sublaws is used.
-/

open scoped BigOperators

namespace WeightedEdgeColoring.SubtwoHarmonicRanks

/-- The unpriced cross-cost inequality for a selected heavy sublaw. -/
theorem profile_cross_cost_of_loads {B : Type*} [Fintype B]
    (mass : B → ℝ) (w : B → Fin 4 → ℝ)
    (selected : B → Prop) [DecidablePred selected] (t : ℝ)
    (hmass : ∀ b, 0 ≤ mass b) (htotal : (∑ b, mass b) ≤ 1)
    (hnonneg : ∀ b i, 0 ≤ w b i) (hload : ∀ b, ∑ i, w b i ≤ 1)
    (hselected : ∀ b, selected b → 1 / 2 < w b 0)
    (ht : t ≤ ∑ b, mass b * harmonicCharge (w b 1)) :
    (∑ b, if selected b then mass b * (harmonicCharge (w b 2) + harmonicCharge (w b 3)) else 0) + t ≤
      1 / 2 + (1 / 2 : ℝ) * (∑ b, if 1 / 2 < w b 1 then mass b else 0) +
        (4 / 21 : ℝ) * ∑ b, if selected b then mass b else 0 := by
  classical
  have hpoint (b : B) :
      (if selected b then harmonicCharge (w b 2) + harmonicCharge (w b 3) else 0) +
        harmonicCharge (w b 1) ≤
      1 / 2 + (if 1 / 2 < w b 1 then (1 / 2 : ℝ) else 0) +
        (if selected b then (4 / 21 : ℝ) else 0) := by
    have hbin : w b 0 + (w b 1 + (w b 2 + w b 3)) ≤ 1 := by
      simpa [Fin.sum_univ_succ] using hload b
    by_cases hb : selected b
    · have hh := hselected b hb
      have hn : ¬1 / 2 < w b 1 := by
        have h₂ := hnonneg b 2
        have h₃ := hnonneg b 3
        linarith
      have hc := triple_charge_half (w b 1) (w b 2) (w b 3)
        (hnonneg b 1) (hnonneg b 2) (hnonneg b 3) (by linarith)
      simp only [if_pos hb, if_neg hn]
      linarith
    · have hw1 : w b 1 ≤ 1 := by
        have h₀ := hnonneg b 0
        have h₂ := hnonneg b 2
        have h₃ := hnonneg b 3
        linarith
      by_cases hj : 1 / 2 < w b 1
      · have hc := charge_le_inv (r := 1) (by decide) (hnonneg b 1) (by simpa using hw1)
        simp only [if_neg hb, if_pos hj]
        norm_num at hc
        linarith
      · have hc := charge_le_inv (r := 2) (by decide) (hnonneg b 1) (le_of_not_gt hj)
        simp only [if_neg hb, if_neg hj]
        norm_num at hc
        linarith
  have havg := Finset.sum_le_sum (s := (Finset.univ : Finset B))
    (fun b _ => mul_le_mul_of_nonneg_left (hpoint b) (hmass b))
  have hrewriteSmall (b : B) :
      mass b * (if selected b then harmonicCharge (w b 2) + harmonicCharge (w b 3) else 0) =
      if selected b then mass b * (harmonicCharge (w b 2) + harmonicCharge (w b 3)) else 0 := by
    split <;> simp
  have hrewriteHeavy (b : B) :
      mass b * (if 1 / 2 < w b 1 then (1 / 2 : ℝ) else 0) =
      (1 / 2 : ℝ) * (if 1 / 2 < w b 1 then mass b else 0) := by
    by_cases h : 1 / 2 < w b 1 <;> simp [h] <;> ring
  have hrewriteSelected (b : B) :
      mass b * (if selected b then (4 / 21 : ℝ) else 0) =
      (4 / 21 : ℝ) * (if selected b then mass b else 0) := by
    by_cases h : selected b <;> simp [h] <;> ring
  simp only [mul_add, Finset.sum_add_distrib, hrewriteSmall, hrewriteHeavy,
    hrewriteSelected, ← Finset.mul_sum, ← Finset.sum_mul] at havg
  simp only [← mul_add] at havg
  nlinarith

/-- Multiplying by a nonnegative price cap gives exactly the generator's
directed small-price / bundle-cost row. -/
theorem priced_profile_cross_cost_of_loads {B : Type*} [Fintype B]
    (mass : B → ℝ) (w : B → Fin 4 → ℝ)
    (selected : B → Prop) [DecidablePred selected] (t sm smallPrice : ℝ)
    (hmass : ∀ b, 0 ≤ mass b) (htotal : (∑ b, mass b) ≤ 1)
    (hnonneg : ∀ b i, 0 ≤ w b i) (hload : ∀ b, ∑ i, w b i ≤ 1)
    (hselected : ∀ b, selected b → 1 / 2 < w b 0)
    (ht : t ≤ ∑ b, mass b * harmonicCharge (w b 1)) (hsm : 0 ≤ sm)
    (hprice : smallPrice ≤ sm *
      ∑ b, if selected b then mass b * (harmonicCharge (w b 2) + harmonicCharge (w b 3)) else 0) :
    smallPrice + sm * t - (sm / 2) * (∑ b, if 1 / 2 < w b 1 then mass b else 0) ≤
      sm / 2 + (4 * sm / 21) * ∑ b, if selected b then mass b else 0 := by
  have h := profile_cross_cost_of_loads mass w selected t hmass htotal hnonneg hload hselected ht
  have hmul := mul_le_mul_of_nonneg_left h hsm
  nlinarith

end WeightedEdgeColoring.SubtwoHarmonicRanks
