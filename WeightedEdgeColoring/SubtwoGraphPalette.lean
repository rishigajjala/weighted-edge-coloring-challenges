import WeightedEdgeColoring.SubtwoWeightedPatterns
import WeightedEdgeColoring.SubtwoPaletteAllocation

/-!
# Reserved palettes of actual weighted graph configurations

The unrestricted configurations obey capacity one at every vertex.
A configuration in the class reserved at `v` has zero multiplicity on
every edge meeting `v`. Every feasible configuration with that property
appears in the reserved class. Thus the finite palette duality applies to
the real weighted coloring problem, without a stronger total-load rule.
-/

open scoped BigOperators

namespace WeightedEdgeColoring.WeightedMultigraph

universe u
variable (G : WeightedMultigraph.{u})

noncomputable def subtwoFullColorPattern
    (p : G.SubtwoWeightedPattern) (e : G.E) : ℝ := p.val e

noncomputable def subtwoAvoidingColorPattern
    (v : G.V) (p : G.SubtwoWeightedPattern) (e : G.E) : ℝ :=
  (p.avoidVertex G v).val e

noncomputable def subtwoReservedColorPattern :
    Option G.V → G.SubtwoWeightedPattern → G.E → ℝ :=
  Subtwo.reservedPalettePattern G.subtwoFullColorPattern G.subtwoAvoidingColorPattern

theorem subtwoReservedColorPattern_nonneg
    (l : Option G.V) (p : G.SubtwoWeightedPattern) (e : G.E) :
    0 ≤ G.subtwoReservedColorPattern l p e := by
  cases l <;> exact Nat.cast_nonneg _

theorem subtwoReservedColorPattern_capacity
    (l : Option G.V) (p : G.SubtwoWeightedPattern) (v : G.V) :
    (∑ e : G.E, if G.Inc v e then G.subtwoReservedColorPattern l p e * G.weight e else 0) ≤ 1 := by
  cases l with
  | none => exact p.property v
  | some w => exact (p.avoidVertex G w).property v

theorem subtwoReservedColorPattern_avoids
    (v : G.V) (p : G.SubtwoWeightedPattern) (e : G.E) (he : G.Inc v e) :
    G.subtwoReservedColorPattern (some v) p e = 0 := by
  change ((p.avoidVertex G v).val e : ℝ) = 0
  rw [p.avoidVertex_zero G v e he]
  simp

/-- Every genuine pattern avoiding `v` is included in the reserved menu. -/
theorem subtwoReservedColorPattern_complete
    (v : G.V) (p : G.SubtwoWeightedPattern)
    (hp : ∀ e, G.Inc v e → p.val e = 0) :
    G.subtwoReservedColorPattern (some v) p = G.subtwoFullColorPattern p := by
  funext e
  change ((p.avoidVertex G v).val e : ℝ) = p.val e
  rw [p.avoidVertex_fixed G v hp]

/-- The maximum price of one actual feasible graph color. -/
noncomputable def subtwoColorPriceMax (price : G.E → ℝ) : ℝ :=
  Subtwo.paletteMaxScore G.subtwoReservedColorPattern price none

/-- The maximum price of a feasible graph color avoiding one vertex. -/
noncomputable def subtwoAvoidingPriceMax (price : G.E → ℝ) (v : G.V) : ℝ :=
  Subtwo.paletteMaxScore G.subtwoReservedColorPattern price (some v)

theorem subtwoAvoidingPriceMax_le (price : G.E → ℝ) (v : G.V) :
    G.subtwoAvoidingPriceMax price v ≤ G.subtwoColorPriceMax price := by
  let p := Subtwo.paletteMaximizer G.subtwoReservedColorPattern price (some v)
  exact Subtwo.patternPrice_le_paletteMaxScore G.subtwoReservedColorPattern price none
    (p.avoidVertex G v)

/-- Exact dual condition for allocating actual weighted-color patterns to
the free palette and the endpoint-reserved palettes. -/
theorem subtwoGraphPalette_iff_chargeInequalities
    (κ : ℝ) (q : G.V → ℝ) (hq : ∀ v, 0 ≤ q v)
    (hsum : (∑ v : G.V, q v) ≤ κ)
    {demand : G.E → ℝ} (hd : ∀ e, 0 ≤ demand e) :
    demand ∈ Subtwo.PaletteAttainable (Subtwo.reservedPaletteBudget κ q)
      G.subtwoReservedColorPattern ↔
    ∀ price : G.E → ℝ, (∀ e, 0 ≤ price e) →
      (∑ e : G.E, price e * demand e) +
        (∑ v : G.V, q v * (G.subtwoColorPriceMax price - G.subtwoAvoidingPriceMax price v)) ≤
          κ * G.subtwoColorPriceMax price := by
  exact Subtwo.reservedPaletteAttainable_iff_chargeInequalities κ q hq hsum
    G.subtwoFullColorPattern G.subtwoAvoidingColorPattern
    (fun _ _ ↦ Nat.cast_nonneg _) (fun _ _ _ ↦ Nat.cast_nonneg _) hd

end WeightedEdgeColoring.WeightedMultigraph
