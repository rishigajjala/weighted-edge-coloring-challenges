import WeightedEdgeColoring.SubtwoFractionalColorPriceBound
import WeightedEdgeColoring.SubtwoVertexRestrictionPatterns
import WeightedEdgeColoring.SubtwoPhysicalNormalizedPrices

/-! The three-vertex half-star bound applied to an induced original
multigraph, with all parallel edge types retained. -/

open scoped BigOperators

namespace WeightedEdgeColoring.WeightedMultigraph

universe u
variable (G : WeightedMultigraph.{u})

theorem inducedTriangle_internalPrice_le
    {n : ℕ} (hn : 0 < n) (hlocal : G.LocallyPacksInto n)
    (S : Finset G.V) (hcard : S.card = 3)
    (price : G.E → ℝ) (hp : ∀ e, 0 ≤ price e) :
    G.subtwoInternalCost price S ≤
      (3/2:ℝ) * (n : ℝ) * G.subtwoColorPriceMax price := by
  let H := G.vertexRestriction S
  let priceH : H.E → ℝ := fun e => price e.1
  have hHcard : Fintype.card H.V = 3 := by
    change Fintype.card (G.vertexRestriction S).V = 3
    rw [G.vertexRestriction_card S, hcard]
  have hlocalH : H.LocallyPacksInto n :=
    G.vertexRestriction_locallyPacksInto S hlocal
  let B := H.localPackingFractionalBins hn hlocalH
  have hpH : ∀ e : H.E, 0 ≤ priceH e := fun e => hp e.1
  have hb := H.triangleLocalBins_price_bound hHcard
    (fun _ : H.E => 1 / (n : ℝ)) priceH B hpH
    (H.localPackingFractionalBins_total hn hlocalH)
  have hmax := G.vertexRestriction_colorPriceMax_le S price
  have hnR : (0 : ℝ) ≤ n := Nat.cast_nonneg _
  have hR0 := G.subtwoColorPriceMax_nonneg price hp
  have hsum : (∑ e : H.E, priceH e * (1 / (n : ℝ))) =
      G.subtwoInternalCost price S / n := by
    calc
      _ = (∑ e : H.E, price e.1) / n := by
        rw [Finset.sum_div]
        apply Finset.sum_congr rfl
        intro e _
        simp [priceH]
        ring
      _ = _ := by rw [G.vertexRestriction_sum S price]
  rw [hsum] at hb
  have hnpos : (0 : ℝ) < n := by exact_mod_cast hn
  have hmul := (div_le_iff₀ hnpos).mp hb
  nlinarith [hmax]

end WeightedEdgeColoring.WeightedMultigraph
