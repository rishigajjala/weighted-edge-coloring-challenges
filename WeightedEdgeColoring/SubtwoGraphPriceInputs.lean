import WeightedEdgeColoring.SubtwoGraphPatternSupports
import WeightedEdgeColoring.SubtwoHighPriceSupports

/-!
# Normalized pair prices from genuine weighted colors

The prices entering the five-vertex certificate are maximum prices of
patterns on vertex pairs, divided by the unrestricted maximum. They lie in
the unit interval and satisfy the disjoint-pair inequalities. Their prices
above one half therefore have the verified star-or-triangle structure.
-/

open scoped BigOperators

namespace WeightedEdgeColoring.WeightedMultigraph

universe u
variable (G : WeightedMultigraph.{u})

theorem subtwoSupportedPriceMax_nonneg
    (S : Finset G.V) (price : G.E → ℝ) (hp : ∀ e, 0 ≤ price e) :
    0 ≤ G.subtwoSupportedPriceMax S price :=
  Subtwo.paletteMaxScore_nonneg (G.subtwoSupportedColorPattern S)
    (fun _ _ _ ↦ Nat.cast_nonneg _) price hp ()

theorem subtwoSupportedPriceMax_le
    (S : Finset G.V) (price : G.E → ℝ) :
    G.subtwoSupportedPriceMax S price ≤ G.subtwoColorPriceMax price := by
  let p := Subtwo.paletteMaximizer (G.subtwoSupportedColorPattern S) price ()
  exact Subtwo.patternPrice_le_paletteMaxScore G.subtwoReservedColorPattern price none
    (p.restrictTo G S)

noncomputable def subtwoNormalizedSetPrice (price : G.E → ℝ) (S : Finset G.V) : ℝ :=
  G.subtwoSupportedPriceMax S price / G.subtwoColorPriceMax price

theorem subtwoNormalizedSetPrice_bounds
    (price : G.E → ℝ) (hp : ∀ e, 0 ≤ price e)
    (hR : 0 < G.subtwoColorPriceMax price) (S : Finset G.V) :
    0 ≤ G.subtwoNormalizedSetPrice price S ∧ G.subtwoNormalizedSetPrice price S ≤ 1 := by
  constructor
  · exact div_nonneg (G.subtwoSupportedPriceMax_nonneg S price hp) hR.le
  · apply (div_le_iff₀ hR).2
    simpa using G.subtwoSupportedPriceMax_le S price

theorem subtwoNormalizedSetPrice_disjoint
    (price : G.E → ℝ) (hR : 0 < G.subtwoColorPriceMax price)
    (S T : Finset G.V) (hST : Disjoint S T) :
    G.subtwoNormalizedSetPrice price S + G.subtwoNormalizedSetPrice price T ≤ 1 := by
  unfold subtwoNormalizedSetPrice
  rw [← add_div]
  apply (div_le_iff₀ hR).2
  simpa using G.subtwo_disjointSupportedPriceMax_add_le S T hST price

/-- The high-price structural reduction now applies to prices obtained
from actual feasible graph configurations, not to an assumed price table. -/
theorem subtwo_graph_highPrice_support_star_or_triangle
    (price : G.E → ℝ) (hR : 0 < G.subtwoColorPriceMax price)
    (F : Finset (Finset G.V)) (hcard : ∀ S ∈ F, S.card = 2)
    (hne : ∃ S ∈ F, (1 / 2 : ℝ) < G.subtwoNormalizedSetPrice price S) :
    (∃ a, ∀ S ∈ F, (1 / 2 : ℝ) < G.subtwoNormalizedSetPrice price S → a ∈ S) ∨
      ∃ a b c, a ≠ b ∧ a ≠ c ∧ b ≠ c ∧
        ∀ S ∈ F, (1 / 2 : ℝ) < G.subtwoNormalizedSetPrice price S →
          S = {a, b} ∨ S = {a, c} ∨ S = {b, c} := by
  exact Subtwo.high_price_support_star_or_triangle F (G.subtwoNormalizedSetPrice price)
    hcard (fun S _ T _ hST ↦ G.subtwoNormalizedSetPrice_disjoint price hR S T hST) hne

end WeightedEdgeColoring.WeightedMultigraph
