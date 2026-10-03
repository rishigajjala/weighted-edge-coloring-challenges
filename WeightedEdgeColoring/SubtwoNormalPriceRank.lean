import WeightedEdgeColoring.SubtwoProfileRankTable

/-!
# The normal-profile price bound

Order the four packet-price caps, without assuming that the physical
loads have that order.  The subset ranks then bound the weighted sum by
`m₀/2 + m₁/2 + m₂/3 + m₃/12`.
-/

open scoped BigOperators

namespace WeightedEdgeColoring.SubtwoHarmonicRanks

theorem four_prefix_price_bound (a m : Fin 4 → ℝ)
    (h₀ : a 0 ≤ 1 / 2) (h₁ : a 0 + a 1 ≤ 1)
    (h₂ : a 0 + a 1 + a 2 ≤ 4 / 3)
    (h₃ : a 0 + a 1 + a 2 + a 3 ≤ 17 / 12)
    (hm₀ : m 1 ≤ m 0) (hm₁ : m 2 ≤ m 1) (hm₂ : m 3 ≤ m 2) (hm₃ : 0 ≤ m 3) :
    (∑ i, m i * a i) ≤ m 0 / 2 + m 1 / 2 + m 2 / 3 + m 3 / 12 := by
  have h0 := mul_le_mul_of_nonneg_left h₀ (sub_nonneg.mpr hm₀)
  have h1 := mul_le_mul_of_nonneg_left h₁ (sub_nonneg.mpr hm₁)
  have h2 := mul_le_mul_of_nonneg_left h₂ (sub_nonneg.mpr hm₂)
  have h3 := mul_le_mul_of_nonneg_left h₃ hm₃
  simp [Fin.sum_univ_succ]
  nlinarith

/-- A normal bin's projected demand prices obey the exact sorted-cap
row of the certificate. The price bounds may come from repeating each
entire projected packet; individual item sizes are irrelevant. -/
theorem normal_sorted_price_bound (w m price : Fin 4 → ℝ)
    (hnonneg : ∀ i, 0 ≤ w i) (hhalf : ∀ i, w i ≤ 1 / 2)
    (hload : ∑ i, w i ≤ 1)
    (hm₀ : m 1 ≤ m 0) (hm₁ : m 2 ≤ m 1) (hm₂ : m 3 ≤ m 2) (hm₃ : 0 ≤ m 3)
    (hprice : ∀ i, price i ≤ m i * harmonicCharge (w i)) :
    (∑ i, price i) ≤ m 0 / 2 + m 1 / 2 + m 2 / 3 + m 3 / 12 := by
  have hc₀ := charge_le_inv (r := 2) (by decide) (hnonneg 0) (hhalf 0)
  have hc₁ := charge_le_inv (r := 2) (by decide) (hnonneg 1) (hhalf 1)
  have hbin : w 0 + w 1 + w 2 + w 3 ≤ 1 := by
    simpa [Fin.sum_univ_succ, add_assoc] using hload
  have hthree := three_normal_charge (Finset.univ : Finset (Fin 3)) ![w 0, w 1, w 2]
    (by simp)
    (by intro i hi; fin_cases i <;> simp [hnonneg])
    (by intro i hi; fin_cases i <;> simpa using hhalf _)
    (by simp [Fin.sum_univ_succ]; linarith [hnonneg 3])
  have hfour := four_normal_charge (Finset.univ : Finset (Fin 4)) w (by simp)
    (fun i _ => hnonneg i) (fun i _ => hhalf i) hload
  simp only [Fin.sum_univ_succ] at hthree hfour
  have hbound := four_prefix_price_bound (fun i => harmonicCharge (w i)) m
    hc₀ (by norm_num at hc₀ hc₁; linarith) (by simpa [add_assoc] using hthree)
    (by simpa [add_assoc] using hfour) hm₀ hm₁ hm₂ hm₃
  exact (Finset.sum_le_sum (fun i _ => hprice i)).trans hbound

end WeightedEdgeColoring.SubtwoHarmonicRanks
