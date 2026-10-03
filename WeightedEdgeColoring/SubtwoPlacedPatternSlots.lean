import WeightedEdgeColoring.SubtwoRoundedBoundaryPlacement
import WeightedEdgeColoring.SubtwoPhysicalPaletteMerge

/-! Transport the integer pattern copies to their actual color names.
The transport preserves type coverage, color capacities, and label avoidance. -/

open scoped BigOperators
namespace WeightedEdgeColoring.Subtwo
noncomputable section

variable {C L P I : Type*} [Fintype C] [DecidableEq C]
  [Fintype L] [DecidableEq L] [Fintype P] [DecidableEq P]
  [Fintype I] [DecidableEq I]

/-- The integer pattern occupying a real color, or the zero pattern when
no rounded pattern was placed there. -/
def placedRoundedPatternSlots (n : ℕ) (a : L × P → ℝ)
    (place : RoundedPaletteColors n a ↪ C) (pattern : L → P → I → ℕ)
    (c : C) (i : I) : ℕ :=
  ∑ p : RoundedPaletteColors n a,
    if place p = c then pattern p.1 p.2.1 i else 0

theorem placedRoundedPatternSlots_at
    (n : ℕ) (a : L × P → ℝ)
    (place : RoundedPaletteColors n a ↪ C) (pattern : L → P → I → ℕ)
    (p : RoundedPaletteColors n a) (i : I) :
    placedRoundedPatternSlots n a place pattern (place p) i = pattern p.1 p.2.1 i := by
  simp [placedRoundedPatternSlots, place.injective.eq_iff]

theorem placedRoundedPatternSlots_unused
    (n : ℕ) (a : L × P → ℝ)
    (place : RoundedPaletteColors n a ↪ C) (pattern : L → P → I → ℕ)
    (c : C) (hc : ∀ p, place p ≠ c) (i : I) :
    placedRoundedPatternSlots n a place pattern c i = 0 := by
  simp [placedRoundedPatternSlots, hc]

/-- Replacing local names by actual palette names loses no integer slots. -/
theorem sum_placedRoundedPatternSlots
    (n : ℕ) (a : L × P → ℝ)
    (place : RoundedPaletteColors n a ↪ C) (pattern : L → P → I → ℕ) (i : I) :
    (∑ c, placedRoundedPatternSlots n a place pattern c i) =
      roundedPaletteSlotCount n pattern a i := by
  unfold placedRoundedPatternSlots
  rw [Finset.sum_comm]
  simp only [Fintype.sum_ite_eq]
  change (∑ p : (Σ l : L, Σ p : P, Fin (roundedPaletteCount n a (l,p))),
    pattern p.1 p.2.1 i) = _
  rw [Fintype.sum_sigma]
  simp only [Fintype.sum_sigma, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
    smul_eq_mul]
  rfl

/-- An injective placement preserves every local weighted capacity. -/
theorem placedRoundedPatternSlots_capacity
    {V : Type*} (n : ℕ) (a : L × P → ℝ)
    (place : RoundedPaletteColors n a ↪ C) (pattern : L → P → I → ℕ)
    (inc : V → I → Prop) [DecidableRel inc] (weight : I → ℝ)
    (hcapacity : ∀ l p v,
      (∑ i, if inc v i then (pattern l p i : ℝ) * weight i else 0) ≤ 1)
    (v : V) (c : C) :
    (∑ i, if inc v i then
      (placedRoundedPatternSlots n a place pattern c i : ℝ) * weight i else 0) ≤ 1 := by
  by_cases hex : ∃ p, place p = c
  · obtain ⟨p, rfl⟩ := hex
    simpa only [placedRoundedPatternSlots_at] using hcapacity p.1 p.2.1 v
  · have hc : ∀ p, place p ≠ c := fun p h => hex ⟨p, h⟩
    simp [placedRoundedPatternSlots_unused n a place pattern c hc]

/-- A placed reserved pattern avoids the endpoint label actually used by
that boundary color. -/
theorem placedRoundedPatternSlots_avoids
    {L : Type*} [Fintype L] [DecidableEq L]
    (n : ℕ) (a : Option L × P → ℝ)
    (place : RoundedPaletteColors n a ↪ C) (pattern : Option L → P → I → ℕ)
    (label : C → Option L)
    (hplace : ∀ p, label (place p) = none ∨ label (place p) = p.1)
    (inc : L → I → Prop)
    (havoid : ∀ l p i, inc l i → pattern (some l) p i = 0)
    (l : L) (c : C) (i : I) (hi : inc l i) (hc : label c = some l) :
    placedRoundedPatternSlots n a place pattern c i = 0 := by
  by_cases hex : ∃ p, place p = c
  · obtain ⟨p, rfl⟩ := hex
    rw [placedRoundedPatternSlots_at]
    have hp : p.1 = some l := by
      rcases hplace p with hn | hh
      · simp [hc] at hn
      · exact hh.symm.trans hc
    exact (congrArg (fun l' => pattern l' p.2.1 i) hp).trans (havoid l p.2.1 i hi)
  · exact placedRoundedPatternSlots_unused n a place pattern c (fun p h => hex ⟨p, h⟩) i

end
end WeightedEdgeColoring.Subtwo
