import WeightedEdgeColoring.SubtwoVertexRestriction
import WeightedEdgeColoring.SubtwoGraphPalette
import WeightedEdgeColoring.SubtwoBlockBounds

/-! Finite sums and feasible patterns transport across vertex restriction. -/

open scoped BigOperators

namespace WeightedEdgeColoring.WeightedMultigraph

universe u
variable (G : WeightedMultigraph.{u}) (S : Finset G.V)

theorem vertexRestriction_sum (f : G.E → ℝ) :
    (∑ e : (G.vertexRestriction S).E, f e.1) =
      G.subtwoInternalCost f S := by
  classical
  unfold subtwoInternalCost
  calc
    (∑ e : (G.vertexRestriction S).E, f e.1) =
        ∑ e ∈ (Finset.univ : Finset G.E).filter
          (fun e => G.fst e ∈ S ∧ G.snd e ∈ S), f e := by
      exact (Finset.sum_subtype
        (p := fun e : G.E => G.fst e ∈ S ∧ G.snd e ∈ S)
        ((Finset.univ : Finset G.E).filter
          (fun e => G.fst e ∈ S ∧ G.snd e ∈ S))
        (by intro e; simp) f).symm
    _ = _ := by rw [Finset.sum_filter]

noncomputable def vertexRestriction_patternLift
    (p : (G.vertexRestriction S).SubtwoWeightedPattern) :
    G.SubtwoWeightedPattern := by
  classical
  refine ⟨fun e => if h : G.fst e ∈ S ∧ G.snd e ∈ S then p.val ⟨e, h⟩ else 0, ?_⟩
  intro v
  by_cases hv : v ∈ S
  · let w : (G.vertexRestriction S).V := ⟨v, hv⟩
    have heq :
        (∑ e : G.E, if G.Inc v e then
          ((if h : G.fst e ∈ S ∧ G.snd e ∈ S then p.val ⟨e, h⟩ else 0 : ℕ) : ℝ) *
            G.weight e else 0) =
          (∑ e : (G.vertexRestriction S).E,
            if (G.vertexRestriction S).Inc w e then
              (p.val e : ℝ) * (G.vertexRestriction S).weight e else 0) := by
      let f : G.E → ℝ := fun e => if G.Inc v e then
        ((if h : G.fst e ∈ S ∧ G.snd e ∈ S then p.val ⟨e, h⟩ else 0 : ℕ) : ℝ) *
          G.weight e else 0
      calc
        _ = G.subtwoInternalCost f S := by
          unfold subtwoInternalCost
          apply Finset.sum_congr rfl
          intro e _
          by_cases h : G.fst e ∈ S ∧ G.snd e ∈ S <;> simp [f, h]
        _ = ∑ e : (G.vertexRestriction S).E, f e.1 :=
          (G.vertexRestriction_sum S f).symm
        _ = _ := by
          apply Finset.sum_congr rfl
          intro e _
          by_cases h : G.Inc v e.1
          · have hH : (G.vertexRestriction S).Inc w e :=
              (G.vertexRestriction_inc S w e).mpr h
            simp only [f, dif_pos e.2, if_pos h, if_pos hH]
            rfl
          · have hH : ¬(G.vertexRestriction S).Inc w e :=
              fun hh => h ((G.vertexRestriction_inc S w e).mp hh)
            simp [f, h, hH]
    rw [heq]
    exact p.property w
  · have hzero : (∑ e : G.E, if G.Inc v e then
        ((if h : G.fst e ∈ S ∧ G.snd e ∈ S then p.val ⟨e, h⟩ else 0 : ℕ) : ℝ) *
          G.weight e else 0) = 0 := by
      apply Finset.sum_eq_zero
      intro e _
      by_cases he : G.Inc v e
      · have hi : ¬(G.fst e ∈ S ∧ G.snd e ∈ S) := by
          intro h
          rcases he with he | he
          · exact hv (he ▸ h.1)
          · exact hv (he ▸ h.2)
        simp [he, hi]
      · simp [he]
    rw [hzero]
    norm_num

theorem vertexRestriction_patternLift_price
    (price : G.E → ℝ)
    (p : (G.vertexRestriction S).SubtwoWeightedPattern) :
    (∑ e : G.E, price e * ((G.vertexRestriction_patternLift S p).val e : ℝ)) =
      ∑ e : (G.vertexRestriction S).E, price e.1 * (p.val e : ℝ) := by
  classical
  let f : G.E → ℝ := fun e => price e *
    ((if h : G.fst e ∈ S ∧ G.snd e ∈ S then p.val ⟨e, h⟩ else 0 : ℕ) : ℝ)
  calc
    _ = G.subtwoInternalCost f S := by
      unfold subtwoInternalCost
      apply Finset.sum_congr rfl
      intro e _
      by_cases h : G.fst e ∈ S ∧ G.snd e ∈ S <;>
        simp [vertexRestriction_patternLift, f, h]
    _ = ∑ e : (G.vertexRestriction S).E, f e.1 :=
      (G.vertexRestriction_sum S f).symm
    _ = _ := by
      apply Finset.sum_congr rfl
      intro e _
      simp [f, e.2]

theorem vertexRestriction_colorPriceMax_le (price : G.E → ℝ) :
    (G.vertexRestriction S).subtwoColorPriceMax (fun e => price e.1) ≤
      G.subtwoColorPriceMax price := by
  let p := Subtwo.paletteMaximizer
    (G.vertexRestriction S).subtwoReservedColorPattern (fun e => price e.1) none
  have h := Subtwo.patternPrice_le_paletteMaxScore
    G.subtwoReservedColorPattern price none
    (G.vertexRestriction_patternLift S p)
  change (∑ e : G.E, price e * ((G.vertexRestriction_patternLift S p).val e : ℝ)) ≤
    G.subtwoColorPriceMax price at h
  rw [G.vertexRestriction_patternLift_price S price p] at h
  exact h

end WeightedEdgeColoring.WeightedMultigraph
