import WeightedEdgeColoring.KempeComponentSwitchAverage
import WeightedEdgeColoring.WeightedMomentPairArray

/-!
# Finite identities for the weighted-moment statistics

For a family of missing palettes `palette i`, the Kempe argument tracks the
weighted one-color statistic `z`, its diagonal correction `d`, and the
off-diagonal two-color statistic `Z`.  This file proves their fixed total
sums.  These identities are independent of the switches because palette
cardinalities are preserved.

We use an ordered symmetric pair array.  Its total is twice the manuscript's
unordered-pair total, so the identity is `W-D` rather than `(W-D)/2`.
-/

namespace WeightedEdgeColoring.WeightedMomentStatistics

open scoped BigOperators
open WeightedEdgeColoring.WeightedMultigraph

noncomputable section

variable {Item Color : Type*}
variable [Fintype Item] [Fintype Color] [DecidableEq Color]

/-- Real cardinality of one item's palette. -/
def paletteSize (palette : Item → Finset Color) (i : Item) : ℝ :=
  (palette i).card

/-- Total item weight. -/
def totalWeight (weight : Item → ℝ) : ℝ := ∑ i, weight i

/-- Harmonic correction `D = sum_i weight_i / |F_i|`. -/
def harmonicWeight (palette : Item → Finset Color)
    (weight : Item → ℝ) : ℝ :=
  ∑ i, weight i / paletteSize palette i

/-- First missing-indicator moment. -/
def firstMoment (palette : Item → Finset Color)
    (weight : Item → ℝ) (c : Color) : ℝ :=
  ∑ i, weight i / paletteSize palette i *
    (if c ∈ palette i then 1 else 0)

/-- Diagonal part of the second moment. -/
def diagonalMoment (palette : Item → Finset Color)
    (weight : Item → ℝ) (c : Color) : ℝ :=
  ∑ i, weight i / (paletteSize palette i) ^ 2 *
    (if c ∈ palette i then 1 else 0)

/-- Ordered off-diagonal second moment. -/
def pairMoment (palette : Item → Finset Color)
    (weight : Item → ℝ) (c d : Color) : ℝ :=
  if c = d then 0 else
    ∑ i, weight i / (paletteSize palette i) ^ 2 *
      (if c ∈ palette i then 1 else 0) *
      (if d ∈ palette i then 1 else 0)

theorem sum_paletteIndicator_eq_card (palette : Finset Color) :
    (∑ c : Color, (if c ∈ palette then (1 : ℝ) else 0)) = palette.card := by
  simp

theorem sum_firstMoment
    (palette : Item → Finset Color) (weight : Item → ℝ)
    (hpalette : ∀ i, 0 < (palette i).card) :
    ∑ c, firstMoment palette weight c = totalWeight weight := by
  unfold firstMoment totalWeight paletteSize
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _hi
  rw [← Finset.mul_sum, sum_paletteIndicator_eq_card]
  have hcard : ((palette i).card : ℝ) ≠ 0 := by
    exact_mod_cast (Nat.ne_of_gt (hpalette i))
  field_simp

theorem sum_diagonalMoment
    (palette : Item → Finset Color) (weight : Item → ℝ)
    (hpalette : ∀ i, 0 < (palette i).card) :
    ∑ c, diagonalMoment palette weight c =
      harmonicWeight palette weight := by
  unfold diagonalMoment harmonicWeight paletteSize
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _hi
  rw [← Finset.mul_sum, sum_paletteIndicator_eq_card]
  have hcard : ((palette i).card : ℝ) ≠ 0 := by
    exact_mod_cast (Nat.ne_of_gt (hpalette i))
  field_simp

/-- Algebraic ordered-off-diagonal identity for an arbitrary real list. -/
theorem sum_offDiagonal_mul (a : Color → ℝ) :
    (∑ c : Color, ∑ d : Color, if c = d then 0 else a c * a d) =
      (∑ c : Color, a c) ^ 2 - ∑ c : Color, (a c) ^ 2 := by
  calc
    (∑ c : Color, ∑ d : Color, if c = d then 0 else a c * a d) =
        ∑ c : Color, a c * ((∑ d : Color, a d) - a c) := by
      apply Finset.sum_congr rfl
      intro c _hc
      calc
        (∑ d : Color, if c = d then 0 else a c * a d) =
            ∑ d : Color, a c * (if c = d then 0 else a d) := by
          apply Finset.sum_congr rfl
          intro d _hd
          by_cases hcd : c = d <;> simp [hcd]
        _ = a c * (∑ d : Color, if c = d then 0 else a d) := by
          rw [← Finset.mul_sum]
        _ = a c * ((∑ d : Color, a d) - a c) := by
          rw [WeightedEdgeColoring.WeightedMomentPairArray.sum_ne_eq_sum_sub a c]
    _ = ∑ c : Color,
          (a c * (∑ d : Color, a d) - (a c) ^ 2) := by
      apply Finset.sum_congr rfl
      intro c _hc
      ring
    _ = (∑ c : Color, a c * (∑ d : Color, a d)) -
          ∑ c : Color, (a c) ^ 2 := by
      simpa only using
        (Finset.sum_sub_distrib (s := (Finset.univ : Finset Color))
          (fun c : Color ↦ a c * (∑ d : Color, a d))
          (fun c : Color ↦ (a c) ^ 2))
    _ = (∑ c : Color, a c) * (∑ d : Color, a d) -
          ∑ c : Color, (a c) ^ 2 := by
      rw [Finset.sum_mul]
    _ = _ := by ring

theorem sum_sq_paletteIndicator_eq_card (palette : Finset Color) :
    (∑ c : Color, (if c ∈ palette then (1 : ℝ) else 0) ^ 2) =
      palette.card := by
  simp

theorem sum_pairMoment
    (palette : Item → Finset Color) (weight : Item → ℝ)
    (hpalette : ∀ i, 0 < (palette i).card) :
    (∑ c : Color, ∑ d : Color, pairMoment palette weight c d) =
      totalWeight weight - harmonicWeight palette weight := by
  unfold pairMoment totalWeight harmonicWeight paletteSize
  calc
    (∑ c : Color, ∑ d : Color,
      if c = d then 0 else
        ∑ i : Item,
          weight i / ((palette i).card : ℝ) ^ 2 *
            (if c ∈ palette i then 1 else 0) *
            (if d ∈ palette i then 1 else 0)) =
        ∑ c : Color, ∑ d : Color, ∑ i : Item,
          if c = d then 0 else
            weight i / ((palette i).card : ℝ) ^ 2 *
              (if c ∈ palette i then 1 else 0) *
              (if d ∈ palette i then 1 else 0) := by
      apply Finset.sum_congr rfl
      intro c _hc
      apply Finset.sum_congr rfl
      intro d _hd
      by_cases hcd : c = d <;> simp [hcd]
    _ = ∑ i : Item, ∑ c : Color, ∑ d : Color,
          if c = d then 0 else
            weight i / ((palette i).card : ℝ) ^ 2 *
              (if c ∈ palette i then 1 else 0) *
              (if d ∈ palette i then 1 else 0) := by
      calc
        (∑ c : Color, ∑ d : Color, ∑ i : Item,
          if c = d then 0 else
            weight i / ((palette i).card : ℝ) ^ 2 *
              (if c ∈ palette i then 1 else 0) *
              (if d ∈ palette i then 1 else 0)) =
            ∑ c : Color, ∑ i : Item, ∑ d : Color,
              if c = d then 0 else
                weight i / ((palette i).card : ℝ) ^ 2 *
                  (if c ∈ palette i then 1 else 0) *
                  (if d ∈ palette i then 1 else 0) := by
          apply Finset.sum_congr rfl
          intro c _hc
          rw [Finset.sum_comm]
        _ = ∑ i : Item, ∑ c : Color, ∑ d : Color,
              if c = d then 0 else
                weight i / ((palette i).card : ℝ) ^ 2 *
                  (if c ∈ palette i then 1 else 0) *
                  (if d ∈ palette i then 1 else 0) := by
          rw [Finset.sum_comm]
    _ = ∑ i : Item, weight i / ((palette i).card : ℝ) ^ 2 *
        (∑ c : Color, ∑ d : Color,
          if c = d then 0 else
            (if c ∈ palette i then 1 else 0) *
            (if d ∈ palette i then 1 else 0)) := by
      apply Finset.sum_congr rfl
      intro i _hi
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro c _hc
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro d _hd
      by_cases hcd : c = d <;> simp [hcd]
    _ = ∑ i : Item,
        (weight i - weight i / ((palette i).card : ℝ)) := by
      apply Finset.sum_congr rfl
      intro i _hi
      rw [sum_offDiagonal_mul
        (fun c : Color ↦ if c ∈ palette i then (1 : ℝ) else 0),
        sum_paletteIndicator_eq_card, sum_sq_paletteIndicator_eq_card]
      have hcard : ((palette i).card : ℝ) ≠ 0 := by
        exact_mod_cast (Nat.ne_of_gt (hpalette i))
      field_simp
    _ = (∑ i : Item, weight i) -
        ∑ i : Item, weight i / ((palette i).card : ℝ) := by
      rw [Finset.sum_sub_distrib]

end

end WeightedEdgeColoring.WeightedMomentStatistics
