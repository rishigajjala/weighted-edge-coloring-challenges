import WeightedEdgeColoring.SubtwoVertexRestrictionPalette
import WeightedEdgeColoring.BPEdgeRestriction

/-! Deleting edge coordinates preserves an attained reserved palette,
with the same endpoint labels and without repeating block selection. -/

open scoped BigOperators
namespace WeightedEdgeColoring.WeightedMultigraph
noncomputable section
universe u
variable (G : WeightedMultigraph.{u}) (R : Finset G.E)

noncomputable def edgeRestriction_patternRestrict (p : G.SubtwoWeightedPattern) :
    (G.edgeRestriction R).SubtwoWeightedPattern := by
  classical
  refine ⟨fun e => p.val e.1, ?_⟩
  intro v
  let term : G.E → ℝ := fun e =>
    if G.Inc v e then (p.val e : ℝ) * G.weight e else 0
  have hsum :
      (∑ e : (G.edgeRestriction R).E,
        if (G.edgeRestriction R).Inc v e then
          (p.val e.1 : ℝ) * (G.edgeRestriction R).weight e else 0) =
      ∑ e ∈ R, term e := by
    symm
    exact Finset.sum_subtype (p := fun e : G.E => e ∈ R) R (by simp) term
  rw [hsum]
  calc
    ∑ e ∈ R, term e ≤ ∑ e : G.E, term e := by
      apply Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
      intro e _ _
      dsimp [term]
      split_ifs
      · exact mul_nonneg (Nat.cast_nonneg _) (G.weight_nonneg _)
      · rfl
    _ ≤ 1 := p.property v

theorem edgeRestriction_reservedPattern
    (l : Option G.V) (p : G.SubtwoWeightedPattern)
    (e : (G.edgeRestriction R).E) :
    (G.edgeRestriction R).subtwoReservedColorPattern l
      (G.edgeRestriction_patternRestrict R p) e =
      G.subtwoReservedColorPattern l p e.1 := by
  classical
  cases l with
  | none => rfl
  | some v =>
    change (((G.edgeRestriction_patternRestrict R p).avoidVertex
      (G.edgeRestriction R) v).val e : ℝ) =
      ((p.avoidVertex G v).val e.val : ℝ)
    simp only [SubtwoWeightedPattern.avoidVertex, SubtwoWeightedPattern.ofLE]
    rfl

theorem edgeRestriction_paletteAttainable
    (budget : Option G.V → ℝ) (demand : G.E → ℝ)
    (hd : demand ∈ Subtwo.PaletteAttainable budget
      G.subtwoReservedColorPattern) :
    (fun e : (G.edgeRestriction R).E => demand e.val) ∈
      Subtwo.PaletteAttainable budget
        (G.edgeRestriction R).subtwoReservedColorPattern := by
  have hproject := Subtwo.paletteAttainable_project budget
    G.subtwoReservedColorPattern (G.edgeRestriction R).subtwoReservedColorPattern
    (fun _ p => G.edgeRestriction_patternRestrict R p)
    (fun (j : (G.edgeRestriction R).E) (i : G.E) =>
      if i = j.val then (1 : ℝ) else 0)
    (by intro j i; dsimp only; split_ifs <;> norm_num)
    (by
      intro l p j
      simpa only [ite_mul, one_mul, zero_mul, Fintype.sum_ite_eq'] using
        G.edgeRestriction_reservedPattern R l p j)
    hd
  simpa only [ite_mul, one_mul, zero_mul, Fintype.sum_ite_eq'] using hproject

end
end WeightedEdgeColoring.WeightedMultigraph
