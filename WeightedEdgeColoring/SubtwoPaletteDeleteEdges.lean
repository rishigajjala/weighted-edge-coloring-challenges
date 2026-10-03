import WeightedEdgeColoring.SubtwoEdgeRestrictionPalette

/-! Deleting edge coordinates from an attained palette gives an attained
palette with exactly zero demand on the deleted edges. -/

open scoped BigOperators
namespace WeightedEdgeColoring.WeightedMultigraph
noncomputable section
universe u
variable (G : WeightedMultigraph.{u}) (R : Finset G.E)

def SubtwoWeightedPattern.keepEdges (p : G.SubtwoWeightedPattern) :
    G.SubtwoWeightedPattern :=
  p.ofLE G (fun e => if e ∈ R then p.val e else 0)
    (by
      classical
      intro e
      by_cases he : e ∈ R <;> simp [he])

theorem keepEdges_reservedPattern
    (l : Option G.V) (p : G.SubtwoWeightedPattern) (e : G.E) :
    G.subtwoReservedColorPattern l (p.keepEdges G R) e =
      if e ∈ R then G.subtwoReservedColorPattern l p e else 0 := by
  classical
  cases l with
  | none =>
    simp [subtwoReservedColorPattern, Subtwo.reservedPalettePattern,
      subtwoFullColorPattern, SubtwoWeightedPattern.keepEdges,
      SubtwoWeightedPattern.ofLE]
  | some v =>
    by_cases hv : G.Inc v e <;> by_cases he : e ∈ R <;>
      simp [subtwoReservedColorPattern, Subtwo.reservedPalettePattern,
        subtwoAvoidingColorPattern, SubtwoWeightedPattern.keepEdges,
        SubtwoWeightedPattern.avoidVertex, SubtwoWeightedPattern.ofLE,
        hv, he]

theorem paletteAttainable_keepEdges
    (budget : Option G.V → ℝ) (demand : G.E → ℝ)
    (hd : demand ∈ Subtwo.PaletteAttainable budget
      G.subtwoReservedColorPattern) :
    (fun e => if e ∈ R then demand e else 0) ∈
      Subtwo.PaletteAttainable budget G.subtwoReservedColorPattern := by
  have hproject := Subtwo.paletteAttainable_project budget
    G.subtwoReservedColorPattern G.subtwoReservedColorPattern
    (fun _ p => p.keepEdges G R)
    (fun j i : G.E => if j = i ∧ j ∈ R then (1 : ℝ) else 0)
    (by
      intro j i
      change 0 ≤ if j = i ∧ j ∈ R then (1 : ℝ) else 0
      split_ifs <;> norm_num)
    (by
      intro l p j
      rw [G.keepEdges_reservedPattern R l p j]
      by_cases hj : j ∈ R <;>
        simp [hj])
    hd
  convert hproject using 1
  funext j
  by_cases hj : j ∈ R <;> simp [hj]

end
end WeightedEdgeColoring.WeightedMultigraph
