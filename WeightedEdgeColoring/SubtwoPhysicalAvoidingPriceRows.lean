import WeightedEdgeColoring.SubtwoPhysicalNormalizedPrices
import WeightedEdgeColoring.SubtwoDenseFiveVariableCaps

/-!
# Avoiding-price rows from actual feasible colors

Two patterns on disjoint vertex sets that exclude a vertex can be added
to form a genuine color avoiding that vertex. This supplies each matching
row used to bound its exterior price loss.
-/

open scoped BigOperators
set_option autoImplicit false

namespace WeightedEdgeColoring.WeightedMultigraph
noncomputable section
universe u
variable (G : WeightedMultigraph.{u})

def subtwoNormalizedAvoidingPrice (price : G.E → ℝ) (v : G.V) : ℝ :=
  G.subtwoAvoidingPriceMax price v / G.subtwoColorPriceMax price

def subtwoAvoidingPriceLoss (q : ℝ) (price : G.E → ℝ) (v : G.V) : ℝ :=
  q * (1 - G.subtwoNormalizedAvoidingPrice price v)

theorem subtwoAvoidingPriceMax_nonneg
    (price : G.E → ℝ) (hp : ∀ e, 0 ≤ price e) (v : G.V) :
    0 ≤ G.subtwoAvoidingPriceMax price v :=
  Subtwo.paletteMaxScore_nonneg G.subtwoReservedColorPattern
    G.subtwoReservedColorPattern_nonneg price hp (some v)

theorem subtwoNormalizedAvoidingPrice_bounds
    (price : G.E → ℝ) (hp : ∀ e, 0 ≤ price e)
    (hR : 0 < G.subtwoColorPriceMax price) (v : G.V) :
    0 ≤ G.subtwoNormalizedAvoidingPrice price v ∧
      G.subtwoNormalizedAvoidingPrice price v ≤ 1 := by
  constructor
  · exact div_nonneg (G.subtwoAvoidingPriceMax_nonneg price hp v) hR.le
  · exact (div_le_one hR).2 (G.subtwoAvoidingPriceMax_le price v)

theorem subtwoAvoidingPriceLoss_bounds
    (q : ℝ) (hq : 0 ≤ q) (price : G.E → ℝ) (hp : ∀ e, 0 ≤ price e)
    (hR : 0 < G.subtwoColorPriceMax price) (v : G.V) :
    0 ≤ G.subtwoAvoidingPriceLoss q price v ∧ G.subtwoAvoidingPriceLoss q price v ≤ q := by
  obtain ⟨hr0, hr1⟩ := G.subtwoNormalizedAvoidingPrice_bounds price hp hR v
  unfold subtwoAvoidingPriceLoss
  constructor
  · exact mul_nonneg hq (sub_nonneg.mpr hr1)
  · nlinarith [mul_nonneg hq hr0]

theorem subtwo_disjointSupportedPriceMax_add_le_avoiding
    (S T : Finset G.V) (hST : Disjoint S T) (v : G.V) (hvS : v ∉ S) (hvT : v ∉ T)
    (price : G.E → ℝ) :
    G.subtwoSupportedPriceMax S price + G.subtwoSupportedPriceMax T price ≤
      G.subtwoAvoidingPriceMax price v := by
  classical
  let p := Subtwo.paletteMaximizer (G.subtwoSupportedColorPattern S) price ()
  let q := Subtwo.paletteMaximizer (G.subtwoSupportedColorPattern T) price ()
  let r := p.addDisjoint G q S T hST
  have hz (e : G.E) (he : G.Inc v e) : r.val e = 0 := by
    change (p.restrictTo G S).val e + (q.restrictTo G T).val e = 0
    rw [p.restrictTo_zero_at_nonmember G S v hvS e he,
      q.restrictTo_zero_at_nonmember G T v hvT e he]
  have h := Subtwo.patternPrice_le_paletteMaxScore G.subtwoReservedColorPattern price (some v) r
  rw [G.subtwoReservedColorPattern_complete v r hz] at h
  change (∑ e : G.E, price e * (r.val e : ℝ)) ≤ G.subtwoAvoidingPriceMax price v at h
  rw [p.addDisjoint_price G q S T hST price] at h
  exact h

theorem subtwoNormalizedSetPrice_disjoint_avoiding
    (price : G.E → ℝ) (hR : 0 < G.subtwoColorPriceMax price)
    (S T : Finset G.V) (hST : Disjoint S T) (v : G.V) (hvS : v ∉ S) (hvT : v ∉ T) :
    G.subtwoNormalizedSetPrice price S + G.subtwoNormalizedSetPrice price T ≤
      G.subtwoNormalizedAvoidingPrice price v := by
  unfold subtwoNormalizedSetPrice subtwoNormalizedAvoidingPrice
  rw [← add_div]
  exact div_le_div_of_nonneg_right
    (G.subtwo_disjointSupportedPriceMax_add_le_avoiding S T hST v hvS hvT price) hR.le

/-- The generator's avoiding-loss row, with the lifted coordinates
interpreted as true products of price and exterior charge. -/
theorem subtwo_physical_avoiding_matching_row
    (q : ℝ) (hq : 0 ≤ q) (price : G.E → ℝ) (hR : 0 < G.subtwoColorPriceMax price)
    (S T : Finset G.V) (hST : Disjoint S T) (v : G.V) (hvS : v ∉ S) (hvT : v ∉ T) :
    G.subtwoAvoidingPriceLoss q price v - q +
      G.subtwoNormalizedSetPrice price S * q + G.subtwoNormalizedSetPrice price T * q ≤ 0 := by
  have h := mul_le_mul_of_nonneg_right
    (G.subtwoNormalizedSetPrice_disjoint_avoiding price hR S T hST v hvS hvT) hq
  unfold subtwoAvoidingPriceLoss
  nlinarith

end
end WeightedEdgeColoring.WeightedMultigraph
