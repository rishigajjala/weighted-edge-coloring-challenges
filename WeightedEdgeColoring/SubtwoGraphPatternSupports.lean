import WeightedEdgeColoring.SubtwoGraphPalette

/-!
# Prices of patterns on disjoint vertex sets

Feasible weighted colors on disjoint vertex sets can be combined into one
color. Consequently their maximum prices add to at most the unrestricted
maximum. This supplies the disjoint-pair price inequalities from actual
weighted configurations.
-/

open scoped BigOperators

namespace WeightedEdgeColoring.WeightedMultigraph

universe u
variable (G : WeightedMultigraph.{u})

namespace SubtwoWeightedPattern

noncomputable def restrictTo (p : G.SubtwoWeightedPattern) (S : Finset G.V) :
    G.SubtwoWeightedPattern := by
  classical
  exact p.ofLE G (fun e ↦ if G.fst e ∈ S ∧ G.snd e ∈ S then p.val e else 0)
    (fun e ↦ by dsimp only; split <;> simp)

theorem restrictTo_zero_at_nonmember
    (p : G.SubtwoWeightedPattern) (S : Finset G.V)
    (v : G.V) (hv : v ∉ S) (e : G.E) (he : G.Inc v e) :
    (p.restrictTo G S).val e = 0 := by
  classical
  have hn : ¬(G.fst e ∈ S ∧ G.snd e ∈ S) := by
    intro hs
    rcases he with he | he
    · exact hv (he ▸ hs.1)
    · exact hv (he ▸ hs.2)
  simp [restrictTo, ofLE, hn]

theorem restrictTo_load_zero
    (p : G.SubtwoWeightedPattern) (S : Finset G.V)
    (v : G.V) (hv : v ∉ S) :
    (∑ e : G.E, if G.Inc v e then ((p.restrictTo G S).val e : ℝ) * G.weight e else 0) = 0 := by
  classical
  apply Finset.sum_eq_zero
  intro e _
  by_cases he : G.Inc v e
  · rw [if_pos he, p.restrictTo_zero_at_nonmember G S v hv e he]
    simp
  · simp [he]

/-- Combine restricted configurations on disjoint vertex sets. -/
noncomputable def addDisjoint
    (p q : G.SubtwoWeightedPattern) (S T : Finset G.V) (hST : Disjoint S T) :
    G.SubtwoWeightedPattern := by
  classical
  refine ⟨fun e ↦ (p.restrictTo G S).val e + (q.restrictTo G T).val e, ?_⟩
  intro v
  have hsplit (e : G.E) :
      (if G.Inc v e then
        (((p.restrictTo G S).val e + (q.restrictTo G T).val e : ℕ) : ℝ) * G.weight e else 0) =
      (if G.Inc v e then ((p.restrictTo G S).val e : ℝ) * G.weight e else 0) +
      (if G.Inc v e then ((q.restrictTo G T).val e : ℝ) * G.weight e else 0) := by
    by_cases he : G.Inc v e <;> simp [he, Nat.cast_add, add_mul]
  simp_rw [hsplit]
  rw [Finset.sum_add_distrib]
  by_cases hv : v ∈ S
  · have ht : v ∉ T := fun ht ↦ (Finset.disjoint_left.mp hST) hv ht
    rw [q.restrictTo_load_zero G T v ht, add_zero]
    exact (p.restrictTo G S).property v
  · rw [p.restrictTo_load_zero G S v hv, zero_add]
    exact (q.restrictTo G T).property v

theorem addDisjoint_price
    (p q : G.SubtwoWeightedPattern) (S T : Finset G.V) (hST : Disjoint S T)
    (price : G.E → ℝ) :
    (∑ e : G.E, price e * ((p.addDisjoint G q S T hST).val e : ℝ)) =
      (∑ e : G.E, price e * ((p.restrictTo G S).val e : ℝ)) +
      ∑ e : G.E, price e * ((q.restrictTo G T).val e : ℝ) := by
  simp [addDisjoint, Nat.cast_add, mul_add, Finset.sum_add_distrib]

end SubtwoWeightedPattern

noncomputable def subtwoSupportedColorPattern (S : Finset G.V) :
    Unit → G.SubtwoWeightedPattern → G.E → ℝ :=
  fun _ p e ↦ (p.restrictTo G S).val e

noncomputable def subtwoSupportedPriceMax (S : Finset G.V) (price : G.E → ℝ) : ℝ :=
  Subtwo.paletteMaxScore (G.subtwoSupportedColorPattern S) price ()

theorem subtwo_disjointSupportedPriceMax_add_le
    (S T : Finset G.V) (hST : Disjoint S T) (price : G.E → ℝ) :
    G.subtwoSupportedPriceMax S price + G.subtwoSupportedPriceMax T price ≤
      G.subtwoColorPriceMax price := by
  let p := Subtwo.paletteMaximizer (G.subtwoSupportedColorPattern S) price ()
  let q := Subtwo.paletteMaximizer (G.subtwoSupportedColorPattern T) price ()
  have h := Subtwo.patternPrice_le_paletteMaxScore G.subtwoReservedColorPattern price none
    (p.addDisjoint G q S T hST)
  change (∑ e : G.E, price e * ((p.addDisjoint G q S T hST).val e : ℝ)) ≤
    G.subtwoColorPriceMax price at h
  rw [p.addDisjoint_price G q S T hST price] at h
  exact h

end WeightedEdgeColoring.WeightedMultigraph
