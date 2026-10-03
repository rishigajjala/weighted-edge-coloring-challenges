import WeightedEdgeColoring.SubtwoItemHarmonic
import WeightedEdgeColoring.SubtwoEndpointPotential
import WeightedEdgeColoring.SubtwoGraphPatternCopies

/-!
# Pointwise estimates for genuine bins

Caps are upper prices for whole feasible packets on each bundle. The
harmonic estimate is applied to individual item copies, with no bound
on the number of types or copies in a bin.
-/

open scoped BigOperators

namespace WeightedEdgeColoring.Subtwo.EndpointPotential

theorem normalized_price_identity (p m t : ℝ)
    (hp : 0 ≤ p) (hm : 0 ≤ m) (hpt : p ≤ m * t) : m * (p / m) = p := by
  by_cases hz : m = 0
  · have hpz : p = 0 := by rw [hz, zero_mul] at hpt; exact le_antisymm hpt hp
    simp [hz, hpz]
  · field_simp

theorem normalized_price_le_charge (p m t : ℝ)
    (hm : 0 ≤ m) (ht : 0 ≤ t) (hpt : p ≤ m * t) : p / m ≤ t := by
  rcases eq_or_lt_of_le hm with hz | hm
  · simp [← hz, ht]
  · exact (div_le_iff₀ hm).mpr (by nlinarith)

/-- A single light item's weighted price is covered by a harmonic term
and its ordinary price. This includes zero-price bundles. -/
theorem light_item_coverage (p m z c h t : ℝ)
    (hp : 0 ≤ p) (hm : 0 ≤ m) (hpt : p ≤ m * t)
    (hz : z ≤ c + h * m) :
    z * (p / m) ≤ c * (p / m) + h * p := by
  have hn : 0 ≤ p / m := div_nonneg hp hm
  have hid := normalized_price_identity p m t hp hm hpt
  have hmul := mul_le_mul_of_nonneg_right hz hn
  calc
    _ ≤ (c + h * m) * (p / m) := hmul
    _ = c * (p / m) + h * (m * (p / m)) := by ring
    _ = _ := by rw [hid]

/-- The no-heavy estimate for an arbitrary multiset of item types. -/
theorem light_bin_estimate {E : Type*} [Fintype E]
    (w p m z : E → ℝ) (n : E → ℕ) (c h : ℝ)
    (hw : ∀ e, 0 ≤ w e) (hp : ∀ e, 0 ≤ p e) (hm : ∀ e, 0 ≤ m e)
    (hc : 0 ≤ c) (hh : 0 ≤ h)
    (hhalf : ∀ e, n e ≠ 0 → w e ≤ 1 / 2)
    (hload : (∑ e, (n e : ℝ) * w e) ≤ 1)
    (hprice : (∑ e, (n e : ℝ) * p e) ≤ 1)
    (hitem : ∀ e, p e ≤ m e * harmonicCharge (w e))
    (hrow : ∀ e, n e ≠ 0 → z e ≤ c + h * m e) :
    (∑ e, (n e : ℝ) * (z e * (p e / m e))) ≤ lightCharge * c + h := by
  have hnorm : (∑ e, (n e : ℝ) * (p e / m e)) ≤ lightCharge := by
    calc
      _ ≤ ∑ e, (n e : ℝ) * harmonicCharge (w e) := by
        exact Finset.sum_le_sum fun e _ ↦ mul_le_mul_of_nonneg_left
          (normalized_price_le_charge (p e) (m e) (harmonicCharge (w e))
            (hm e) (harmonicCharge_nonneg _) (hitem e)) (Nat.cast_nonneg _)
      _ ≤ lightCharge := ItemHarmonic.light_unit_charge_counts w n hw hhalf hload
  have hcoverage : (∑ e, (n e : ℝ) * (z e * (p e / m e))) ≤
      c * (∑ e, (n e : ℝ) * (p e / m e)) + h * (∑ e, (n e : ℝ) * p e) := by
    rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
    apply Finset.sum_le_sum
    intro e _
    by_cases hn : n e = 0
    · simp [hn]
    · have hi := mul_le_mul_of_nonneg_left
        (light_item_coverage (p e) (m e) (z e) c h (harmonicCharge (w e))
          (hp e) (hm e) (hitem e) (hrow e hn)) (Nat.cast_nonneg (n e))
      nlinarith [hi]
  exact noHeavy_bound _ _ _ c h lightCharge hc hh hcoverage hnorm hprice

/-- A light remainder of total load at most one half has bounded
normalized profit, even when some bundle caps are zero. -/
theorem residual_normalized_price {E : Type*} [Fintype E]
    (w p m : E → ℝ) (n : E → ℕ)
    (hw : ∀ e, 0 ≤ w e) (hm : ∀ e, 0 ≤ m e)
    (hload : (∑ e, (n e : ℝ) * w e) ≤ 1 / 2)
    (hitem : ∀ e, p e ≤ m e * harmonicCharge (w e)) :
    (∑ e, (n e : ℝ) * (p e / m e)) ≤ residualCharge := by
  calc
    _ ≤ ∑ e, (n e : ℝ) * harmonicCharge (w e) := by
      exact Finset.sum_le_sum fun e _ ↦ mul_le_mul_of_nonneg_left
        (normalized_price_le_charge (p e) (m e) (harmonicCharge (w e))
          (hm e) (harmonicCharge_nonneg _) (hitem e)) (Nat.cast_nonneg _)
    _ ≤ residualCharge := ItemHarmonic.residual_charge_counts w n hw hload

/-- Cover every light remainder term, keeping shared-bundle profit
separate. This is the finite-sum step behind the paired-heavy estimate. -/
theorem remainder_coverage {E : Type*} [Fintype E]
    (p m z t : E → ℝ) (n : E → ℕ) (shared : E → Prop) [DecidablePred shared]
    (m₀ z₀ alpha rho : ℝ)
    (hp : ∀ e, 0 ≤ p e) (hm : ∀ e, 0 ≤ m e)
    (hitem : ∀ e, p e ≤ m e * t e)
    (hsame : ∀ e, shared e → m e = m₀ ∧ z e = z₀)
    (hoff : ∀ e, n e ≠ 0 → ¬shared e → z e - rho * m e ≤ alpha) :
    (∑ e, (n e : ℝ) * (z e * (p e / m e))) ≤
      rho * (∑ e, (n e : ℝ) * (if shared e then 0 else p e)) +
      alpha * (∑ e, (n e : ℝ) * (p e / m e)) +
      max (z₀ - alpha) 0 / m₀ *
        (∑ e, (n e : ℝ) * (if shared e then p e else 0)) := by
  simp_rw [Finset.mul_sum, ← Finset.sum_add_distrib]
  apply Finset.sum_le_sum
  intro e _
  by_cases hn : n e = 0
  · simp [hn]
  have hn0 : 0 ≤ (n e : ℝ) := Nat.cast_nonneg _
  have hnorm : 0 ≤ p e / m e := div_nonneg (hp e) (hm e)
  by_cases hs : shared e
  · obtain ⟨hmc, hzc⟩ := hsame e hs
    have hmax : z₀ ≤ alpha + max (z₀ - alpha) 0 := by
      have := le_max_left (z₀ - alpha) 0
      linarith
    have hitem' := mul_le_mul_of_nonneg_right hmax (by simpa [hmc] using hnorm)
    have hcount := mul_le_mul_of_nonneg_left hitem' hn0
    simp only [hs, if_true, mul_zero, zero_add, hmc, hzc]
    convert hcount using 1 <;> ring
  · have hid := normalized_price_identity (p e) (m e) (t e) (hp e) (hm e) (hitem e)
    have hcoef : z e ≤ alpha + rho * m e := by linarith [hoff e hn hs]
    have hitem' : z e * (p e / m e) ≤ alpha * (p e / m e) + rho * p e := by
      calc
        _ ≤ (alpha + rho * m e) * (p e / m e) := mul_le_mul_of_nonneg_right hcoef hnorm
        _ = alpha * (p e / m e) + rho * (m e * (p e / m e)) := by ring
        _ = _ := by rw [hid]
    have hcount := mul_le_mul_of_nonneg_left hitem' hn0
    simp only [hs, if_false, mul_zero, add_zero]
    nlinarith [hcount]

end WeightedEdgeColoring.Subtwo.EndpointPotential

namespace WeightedEdgeColoring.WeightedMultigraph

universe u
variable (G : WeightedMultigraph.{u})

/-- Repeating one item proves the item-level bound from the actual
maximum packet price of its bundle. -/
theorem subtwo_item_price_le_bundle_harmonic (price : G.E → ℝ) (e : G.E) :
    price e ≤ G.subtwoSupportedPriceMax {G.fst e, G.snd e} price *
      harmonicCharge (G.weight e) := by
  classical
  have h := G.subtwo_pattern_price_le_harmonic_charge
    (SubtwoWeightedPattern.single G e) {G.fst e, G.snd e} ?_ ?_ price
  · simpa [SubtwoWeightedPattern.single_price, SubtwoWeightedPattern.single,
      SubtwoWeightedPattern.ofTotalLoad] using h
  · intro f hf
    have he : f = e := by
      by_contra he
      exact hf (by simp [SubtwoWeightedPattern.single, SubtwoWeightedPattern.ofTotalLoad, he])
    subst f
    simp
  · simpa [SubtwoWeightedPattern.single, SubtwoWeightedPattern.ofTotalLoad]
      using G.weight_le_one e

end WeightedEdgeColoring.WeightedMultigraph
