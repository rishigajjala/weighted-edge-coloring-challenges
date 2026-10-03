import WeightedEdgeColoring.SubtwoBoundaryPalettePadding
import WeightedEdgeColoring.SubtwoLabelRounding

/-!
# Placing rounded local palettes among the actual color names

If each used boundary label exceeds its fractional budget by at most D,
then |L|(D+1) extra colors suffice for every rounded local allocation. This
bound is local to a block and so is independent of the number of blocks.
-/

open scoped BigOperators
namespace WeightedEdgeColoring.Subtwo
noncomputable section

variable {C L P : Type*} [Fintype C] [Fintype L] [DecidableEq L]
  [Fintype P] [DecidableEq P]

/-- Round and place the local reserved classes in the real palette. All
existing nonempty boundary labels are preserved by the placement. -/
theorem exists_roundedReservedPalettePlacement
    (n D : ℕ) (κ : ℝ) (q : L → ℝ)
    (hq : ∀ l, 0 ≤ q l) (hsum : (∑ l, q l) ≤ κ)
    (a : Option L × P → ℝ)
    (ha : PaletteFeasible (reservedPaletteBudget κ q) a)
    (label : C → Option L)
    (hlabel : ∀ l,
      (Fintype.card {c : C // label c = some l} : ℝ) ≤ (n : ℝ) * q l + D)
    (hpalette : (n : ℝ) * κ + (Fintype.card L : ℝ) * (D + 1) ≤ Fintype.card C) :
    ∃ place : RoundedPaletteColors n a ↪ C,
      ∀ p, label (place p) = none ∨ label (place p) = p.1 := by
  classical
  let m : L → ℕ := fun l => Nat.ceil ((n : ℝ) * q l) + D
  have hm : ∀ l, (m l : ℝ) ≤ (n : ℝ) * q l + (D + 1) := by
    intro l
    have hc := (Nat.ceil_lt_add_one (mul_nonneg (Nat.cast_nonneg n) (hq l))).le
    dsimp [m]
    push_cast
    linarith
  have hmsum : ((∑ l, m l : ℕ) : ℝ) ≤
      (n : ℝ) * ∑ l, q l + (Fintype.card L : ℝ) * (D + 1) := by
    rw [Nat.cast_sum]
    calc
      (∑ l, (m l : ℝ)) ≤ ∑ l, ((n : ℝ) * q l + (D + 1)) :=
        Finset.sum_le_sum (fun l _ => hm l)
      _ = _ := by simp [Finset.sum_add_distrib, Finset.mul_sum]; ring
  have htotal : (∑ l, m l) ≤ Fintype.card C := by
    have hmult := mul_le_mul_of_nonneg_left hsum (Nat.cast_nonneg n)
    have hh : ((∑ l, m l : ℕ) : ℝ) ≤ Fintype.card C := by linarith
    exact_mod_cast hh
  have hcount : ∀ l, Fintype.card {c : C // label c = some l} ≤ m l := by
    intro l
    have hc := Nat.le_ceil ((n : ℝ) * q l)
    have hh := hlabel l
    have hreal : (Fintype.card {c : C // label c = some l} : ℝ) ≤ (m l : ℝ) := by
      dsimp [m]
      push_cast
      linarith
    exact_mod_cast hreal
  apply exists_reservedPalettePlacement label m hcount htotal
    (RoundedLabelColors n a)
  intro l
  cases l with
  | some l =>
    have hl := (roundedReservedPalette_class_bounds n κ q P a ha).2 l
    exact hl.trans ((Nat.floor_le_ceil _).trans (Nat.le_add_right _ _))
  | none =>
    have hcommon := (roundedReservedPalette_class_bounds n κ q P a ha).1
    have hnonneg : 0 ≤ (n : ℝ) * (κ - ∑ l, q l) :=
      mul_nonneg (Nat.cast_nonneg _) (sub_nonneg.mpr hsum)
    have hfloor := Nat.floor_le hnonneg
    have hremaining :
        Nat.floor ((n : ℝ) * (κ - ∑ l, q l)) ≤ Fintype.card C - ∑ l, m l := by
      have hreal :
          (Nat.floor ((n : ℝ) * (κ - ∑ l, q l)) : ℝ) ≤
            ((Fintype.card C - ∑ l, m l : ℕ) : ℝ) := by
        rw [Nat.cast_sub htotal]
        nlinarith
      exact_mod_cast hreal
    exact hcommon.trans hremaining

end
end WeightedEdgeColoring.Subtwo
